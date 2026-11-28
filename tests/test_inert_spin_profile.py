"""Mixed-return inert spins: optional typed named data, terminal tails and no-return call loops."""

import argparse
from contextlib import redirect_stdout
import hashlib
import io
import json
import os
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match
import report_fixtures
import match_evidence as evidence
import inert_spin_profile as profile

A, B = 0x08010000, 0x08020000
OBJECTS = {"data_03000100": "0x03000100"}
TAIL_SOURCE = """extern unsigned char data_03000100[];
extern int func_08020000(int);

int func_08010000(int value)
{
    if (value == 15) {
        data_03000100[0] = 0xA3;
        data_03000100[1] = 0x5D;
        for (;;)
            ;
    }
    return func_08020000(value) + data_03000100[2];
}
"""
ADDEND_SOURCE = """extern int data_03000100[];
extern int data_03000200[];
extern int func_08020000(int *);

int func_08010000(int value)
{
    if (value == 15)
        for (;;)
            ;
    return func_08020000(&data_03000100[4]) + func_08020000(&data_03000200[-1]);
}
"""
PARAMETER_SOURCE = """int func_08010000(unsigned char *state, int value)
{
    if (value == 15) {
        state[0] = 0xA3;
        state[1] = 0x5D;
        for (;;)
            ;
    }
    return state[2] + value;
}
"""
FUNCTION_SOURCE = """extern int func_08020000(int);
typedef int (*Handler)(int);

Handler func_08010000(int value)
{
    if (value == 15)
        for (;;)
            ;
    return func_08020000;
}
"""
PLAIN_SOURCE = """extern int func_08020000(int);

int func_08010000(int value)
{
    if (value == 15)
        for (;;)
            ;
    return func_08020000(value);
}
"""
LOOP_SOURCE = """extern unsigned char data_03000100[];
extern void func_08020000(void);

void func_08010000(void)
{
    data_03000100[0] = 0xA3;
    data_03000100[1] = 0x5D;
    for (;;)
        func_08020000();
}
"""
# A fixed frame with saved high registers and spills, a prefix call, stack reloads and three calls in the loop.
FRAMED_LOOP_SOURCE = """extern void func_08020000(int, int, int, int);

void func_08010000(int a, int b, int c, int d)
{
    int e = a + b, f = b + c, g = c + d, h = d + a, i = a + c, j = b + d;

    func_08020000(a, b, c, d);
    for (;;) {
        func_08020000(e, f, g, h);
        func_08020000(i, j, a, b);
        func_08020000(c, d, e + 1, f + 1);
    }
}
"""
LOOP_REFUSALS = {
    "store in the loop": ("""extern unsigned char data_03000100[];
extern void func_08020000(void);

void func_08010000(void)
{
    for (;;) {
        data_03000100[0] = 1;
        func_08020000();
    }
}
""", "call loop excludes stores"),
    "stack argument store in the loop": ("""extern void func_08020000(int, int, int, int, int);

void func_08010000(void)
{
    for (;;)
        func_08020000(1, 2, 3, 4, 5);
}
""", "call loop excludes stores"),
    "conditional in the loop": ("""extern unsigned char data_03000100[];
extern int func_08020000(void);

void func_08010000(void)
{
    for (;;)
        if (func_08020000())
            data_03000100[0] = 1;
}
""", "fall straight through"),
    "second cycle": ("""extern unsigned char data_03000100[];
extern void func_08020000(void);

void func_08010000(void)
{
    for (;;) {
        func_08020000();
        while (data_03000100[0])
            ;
    }
}
""", "fall straight through"),
    "return path": ("""extern void func_08020000(void);

void func_08010000(int value)
{
    if (value == 15)
        return;
    for (;;)
        func_08020000();
}
""", "terminal tails must be straight-line"),
    "call after a spin-only cycle": ("""extern unsigned char data_03000100[];
extern void func_08020000(void);

void func_08010000(void)
{
    func_08020000();
    data_03000100[0] = 0xA3;
    for (;;)
        ;
}
""", "requires a typed call inside the cycle"),
}
# cmp r0,#15; beq 6; bx lr; movs r1,#0xA3; strb r1,[r2]; b .
TAIL = [0x280F, 0xD000, 0x4770, 0x21A3, 0x7011, 0xE7FE]
# cmp r0,#15; beq 6; bx lr; ldr r1,[pc,#8]; movs r2,#0xA3; strb r2,[r1]; b .; nop;
# then two copies of the object address, only the first of which is loaded.
POOL = [0x280F, 0xD000, 0x4770, 0x4902, 0x22A3, 0x700A, 0xE7FE, 0x46C0]


def body(words, literals=()):
    return b"".join(struct.pack("<H", word) for word in words) + \
        b"".join(struct.pack("<I", word) for word in literals)


def bl(site, target):
    offset = target - (site + 4)
    return [0xF000 | (offset >> 12) & 0x7FF, 0xF800 | (offset >> 1) & 0x7FF]


def indexes(size):
    rows = [{"rom": f"0x{A:08X}", "end": f"0x{A + size:08X}", "mode": "thumb", "instrs": 1},
            {"rom": f"0x{B:08X}", "end": f"0x{B + 2:08X}", "mode": "thumb", "instrs": 1}]
    return json.dumps(rows).encode(), "".join(
        f"{int(r['rom'], 16):08X} {int(r['end'], 16):08X} "
        f"{int(r['end'], 16) - int(r['rom'], 16)} {r['instrs']} return\n" for r in rows).encode()


def image(data):
    rom = bytearray(B - match.ROM_BASE + 2)
    rom[A - match.ROM_BASE:A - match.ROM_BASE + len(data)] = data
    return bytes(rom)


def branch(site, target):
    return 0xE000 | ((target - (site + 4)) >> 1) & 0x7FF


# push {lr}; then the loop: movs r0,#1; bl B; b back to the movs.
LOOP = [0xB500, 0x2001] + bl(A + 4, B) + [branch(A + 8, A + 2)]
LOOP_CALLS = {A + 4: B}
LOOP_RECORD = {"branch": 8, "calls": [4], "head": 2}
LOOP_MANIFEST = {"calls": [[4, "func_08020000"]], "frame": False, "loop": LOOP_RECORD, "spins": []}


class TerminalTailTests(unittest.TestCase):
    """The walker and the profile's manifest check, on exact Thumb encodings."""

    def walk(self, words, calls=None, context=None):
        return match.verify_leaf_instructions(body(words), A, True, calls or {},
                                              inert_spin_context={"tails": []} if context is None else context)

    def verify(self, data, manifest, objects=None):
        mapping, index = indexes(len(data))
        return profile.verify(data, A, image(data), mapping, index, manifest,
                              data_mapping=None if objects is None else json.dumps(objects).encode())

    def test_store_prefix_before_self_branch_is_a_terminal_tail(self):
        context = {"tails": []}
        self.walk(TAIL, context=context)
        self.assertEqual(context, {"spins": [10], "tails": [6, 8]})
        manifest = {"calls": [], "frame": False, "spins": [10], "tails": [6, 8]}
        self.assertEqual(len(self.verify(body(TAIL), manifest)), 6)
        self.assertEqual(profile.summary(manifest), profile.TAIL_SUMMARY)

    def test_tails_are_opt_in_and_bound_by_the_manifest(self):
        # The software-double record and the old manifest keep the self-branch-only rule.
        with self.assertRaisesRegex(ValueError, "must itself be an inert narrow self-branch"):
            self.walk(TAIL, context={})
        for context in ({"tails": [6]}, {"tails": ()}, {"spins": []}, {"tails": [], "spins": []}):
            with self.subTest(context=context), self.assertRaisesRegex(ValueError, "fresh isolated"):
                self.walk(TAIL, context=context)
        for tails in (None, [6], [8], [8, 6], [6, 8, 10], [6, 6, 8], [], [True, 8], [6.0, 8]):
            manifest = {"calls": [], "frame": False, "spins": [10]}
            if tails is not None:
                manifest["tails"] = tails
            with self.subTest(tails=tails), self.assertRaises(ValueError):
                self.verify(body(TAIL), manifest)
        spin = [0x280F, 0xD000, 0x4770, 0xE7FE]
        context = {"tails": []}
        self.walk(spin, context=context)
        self.assertEqual(context, {"spins": [6], "tails": []})
        self.verify(body(spin), {"calls": [], "frame": False, "spins": [6]})
        with self.assertRaises(ValueError):
            self.verify(body(spin), {"calls": [], "frame": False, "spins": [6], "tails": [6]})

    def test_branches_calls_stack_changes_and_indirect_transfers_in_a_tail_refuse(self):
        cases = {
            "conditional": (TAIL[:4] + [0xD0FF] + TAIL[5:], "straight-line"),
            "stack adjustment": (TAIL[:4] + [0xB081] + TAIL[5:], "straight-line"),
            "push": (TAIL[:4] + [0xB410] + TAIL[5:], "straight-line"),
            "register to sp": (TAIL[:4] + [0x468D] + TAIL[5:], None),
            "indirect": (TAIL[:4] + [0x4708] + TAIL[5:], None),
            "pc write": (TAIL[:4] + [0x468F] + TAIL[5:], None),
            "interrupt": (TAIL[:4] + [0xDF00] + TAIL[5:], None),
            "two-instruction cycle": (TAIL[:5] + [0xE7FD], "straight-line"),
            "forward branch": (TAIL[:4] + [0xE000, 0x46C0, 0xE7FE], "straight-line"),
        }
        for name, (words, message) in cases.items():
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message or ""):
                self.walk(words)
        call = TAIL[:3] + bl(A + 6, B) + [0xE7FE]
        with self.assertRaisesRegex(ValueError, "straight-line"):
            self.walk(call, calls={A + 6: B})
        # ldr r1,[pc,#4]; add sp,r1 with the literal -8: a literal stack adjustment.
        literal = TAIL[:3] + [0x4901, 0x448D, 0xE7FE]
        with self.assertRaisesRegex(ValueError, "straight-line"):
            match.verify_leaf_instructions(body(literal, (0xFFFFFFF8,)), A, True, {},
                                           inert_spin_context={"tails": []})

    def test_a_function_without_a_return_is_still_refused(self):
        with self.assertRaisesRegex(ValueError, "no verified return"):
            self.walk([0x21A3, 0x7011, 0xE7FE])
        with self.assertRaisesRegex(ValueError, "no verified return"):
            self.walk([0xE7FE])

    def test_typed_data_record_binds_aligned_loaded_mapped_words(self):
        data = body(POOL, (0x03000100, 0x03000100))
        manifest = {"calls": [], "data": [[16, "data_03000100", 0]], "frame": False,
                    "spins": [12], "tails": [6, 8, 10]}
        self.verify(data, manifest, OBJECTS)
        for addend in (-4, 16):
            changed = body(POOL, (0x03000100 + addend, 0x03000100))
            with self.subTest(addend=addend):
                self.verify(changed, dict(manifest, data=[[16, "data_03000100", addend]]), OBJECTS)
        refusals = {
            "not loaded": ([[20, "data_03000100", 0]], OBJECTS, "PC-relative"),
            "misaligned": ([[18, "data_03000100", 0]], OBJECTS, "aligned"),
            "unmapped": ([[16, "data_03000200", 0]], OBJECTS, "mapped"),
            "wrong addend": ([[16, "data_03000100", 4]], OBJECTS, "differs"),
            "duplicate": ([[16, "data_03000100", 0]] * 2, OBJECTS, "ordered"),
            "float addend": ([[16, "data_03000100", 0.0]], OBJECTS, "mapped"),
            "boolean offset": ([[True, "data_03000100", 0]], OBJECTS, "mapped"),
            "short": ([[16, "data_03000100"]], OBJECTS, "binding"),
            "empty": ([], OBJECTS, "manifest"),
            "no data map": ([[16, "data_03000100", 0]], None, "manifest"),
            "own function": ([[16, "data_self", 0]], {"data_self": f"0x{A:08X}"}, "own function"),
        }
        for name, (records, objects, message) in refusals.items():
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message):
                self.verify(data, dict(manifest, data=records), objects)
        own = body(POOL, (A, A))
        with self.assertRaisesRegex(ValueError, "own function"):
            self.verify(own, dict(manifest, data=[[16, "data_self", 0]]), {"data_self": f"0x{A:08X}"})

    def test_reports_without_records_keep_their_digest(self):
        manifest = {"calls": [], "frame": False, "spins": [6]}
        arguments = (A, body([0x280F, 0xD000, 0x4770, 0xE7FE]), manifest, "0" * 64, b"[]", b"")
        self.assertEqual(profile.fingerprint(*arguments),
                         profile.fingerprint(*arguments, data_mapping=json.dumps(OBJECTS).encode()))
        digest = hashlib.sha256()
        for payload in (profile.SCHEMA.encode(), A.to_bytes(4, "little"), arguments[1],
                        profile.manifest_text(manifest).encode(), arguments[3].encode(),
                        hashlib.sha256(b"[]").hexdigest().encode(), hashlib.sha256(b"").hexdigest().encode(),
                        profile.compiler_text().encode()):
            digest.update(len(payload).to_bytes(8, "little"))
            digest.update(payload)
        self.assertEqual(profile.fingerprint(*arguments), digest.hexdigest())
        self.assertEqual(profile.summary(manifest), profile.SUMMARY)
        typed = dict(manifest, data=[[16, "data_03000100", 0]])
        with self.assertRaisesRegex(ValueError, "exact data mapping"):
            profile.fingerprint(*arguments[:2], typed, *arguments[3:])
        self.assertNotEqual(
            profile.fingerprint(*arguments[:2], typed, *arguments[3:], data_mapping=json.dumps(OBJECTS).encode()),
            profile.fingerprint(*arguments[:2], typed, *arguments[3:],
                                data_mapping=json.dumps(dict(OBJECTS, data_03000200="0x03000200")).encode()))


class CallLoopTests(unittest.TestCase):
    """A function with no return whose only cycle is one loop of typed calls, on exact Thumb encodings."""

    def walk(self, words, calls=None, context=None, literals=()):
        context = {"tails": [], "loop": None} if context is None else context
        match.verify_leaf_instructions(body(words, literals), A, True, LOOP_CALLS if calls is None else calls,
                                       inert_spin_context=context)
        return context

    def verify(self, data, manifest):
        mapping, index = indexes(len(data))
        return profile.verify(data, A, image(data), mapping, index, manifest)

    def test_call_loop_is_recorded_and_bound_by_the_manifest(self):
        self.assertEqual(self.walk(LOOP), {"spins": [], "tails": [], "loop": LOOP_RECORD})
        self.assertEqual(len(self.verify(body(LOOP), LOOP_MANIFEST)), 4)
        self.assertEqual(profile.summary(LOOP_MANIFEST), profile.LOOP_SUMMARY)
        self.assertEqual(profile.control_flow(LOOP_MANIFEST), profile.LOOP_CONTROL_FLOW)
        self.assertEqual(profile.make_manifest(LOOP_CALLS, A, [], {"spins": [], "tails": [], "loop": LOOP_RECORD}),
                         LOOP_MANIFEST)

    def test_prefix_calls_loads_and_a_loop_at_the_entry_are_admitted(self):
        # push; bl B; movs r0,#1; bl B; b back to the movs: the first call is in the prefix.
        prefix = [0xB500] + bl(A + 2, B) + [0x2001] + bl(A + 8, B) + [branch(A + 12, A + 6)]
        self.assertEqual(self.walk(prefix, {A + 2: B, A + 8: B})["loop"],
                         {"branch": 12, "calls": [8], "head": 6})
        # movs r0,#1; bl B; b to the entry: no prefix at all.
        entry = [0x2001] + bl(A + 2, B) + [branch(A + 6, A)]
        self.assertEqual(self.walk(entry, {A + 2: B})["loop"], {"branch": 6, "calls": [2], "head": 0})
        # push; ldr r0,[pc]; ldr r0,[r0]; bl B; b back to the first load; then the pool word.
        loads = [0xB500, 0x4802, 0x6800] + bl(A + 6, B) + [branch(A + 10, A + 2), 0x46C0]
        self.assertEqual(self.walk(loads, {A + 6: B}, literals=(0x03000100,))["loop"],
                         {"branch": 10, "calls": [6], "head": 2})

    def test_call_loop_is_opt_in(self):
        for context in ({}, {"tails": []}):
            with self.subTest(context=context), self.assertRaisesRegex(ValueError, "no verified return"):
                self.walk(LOOP, context=context)
        for context in ({"loop": None}, {"tails": [], "loop": {}}, {"tails": [], "loop": False},
                        {"tails": [], "loop": LOOP_RECORD}, {"tails": [6], "loop": None}):
            with self.subTest(context=context), self.assertRaisesRegex(ValueError, "fresh isolated"):
                self.walk(LOOP, context=context)
        # A function with a return keeps its spins and tails and records no loop.
        context = {"tails": [], "loop": None}
        match.verify_leaf_instructions(body(TAIL), A, True, {}, inert_spin_context=context)
        self.assertEqual(context, {"spins": [10], "tails": [6, 8], "loop": None})

    def test_spin_without_a_call_in_its_cycle_is_still_refused(self):
        for words, calls in (([0xE7FE], {}), ([0x21A3, 0x7011, 0xE7FE], {}), ([0xB500, 0x2001, 0xE7FE], {}),
                             ([0xB500] + bl(A + 2, B) + [0xE7FE], {A + 2: B})):
            with self.subTest(words=words), self.assertRaisesRegex(ValueError, "typed call inside the cycle"):
                self.walk(words, calls)

    def test_loop_and_prefix_mutations_refuse(self):
        call = bl(A + 4, B)
        close = [branch(A + 8, A + 2)]
        cases = {
            "str in the loop": ([0xB500, 0x6008] + call + close, "excludes stores"),
            "strb in the loop": ([0xB500, 0x7008] + call + close, "excludes stores"),
            "strh in the loop": ([0xB500, 0x8008] + call + close, "excludes stores"),
            "stmia in the loop": ([0xB500, 0xC101] + call + close, "excludes stores"),
            # push {lr} leaves only the LR word, so the frame walk refuses this store first.
            "stack store in the loop": ([0xB500, 0x9000] + call + close,
                                        "excludes stores|stack-frame store overlaps a saved register"),
            "balanced sp change in the loop": ([0xB500, 0xB081, 0xB001] + bl(A + 6, B) +
                                               [branch(A + 10, A + 2)], "stack-pointer changes"),
            "push and pop in the loop": ([0xB500, 0xB401, 0xBC01] + bl(A + 6, B) + [branch(A + 10, A + 2)],
                                         "stack-pointer changes"),
            # The loop starts at the entry, so the entry instruction is itself in the loop.
            "store at the entry of a loop at the entry": ([0x6008] + bl(A + 2, B) + [branch(A + 6, A)],
                                                          "excludes stores"),
            # The walker itself refuses these before the loop rule runs.
            "unbalanced sp change in the loop": ([0xB500, 0xB081] + call + close, "inconsistent saved stack depth"),
            "conditional in the loop": ([0xB500, 0xD0FF] + call + close, "fall straight through"),
            # push; cmp r0,#0; beq to a spin; bl B; b back to the cmp; b .: a conditional exit and a second cycle.
            "conditional exit to a spin": ([0xB500, 0x2800, 0xD002] + bl(A + 6, B) +
                                           [branch(A + 10, A + 2), 0xE7FE], "fall straight through"),
            "forward branch in the prefix": ([0xB500, branch(A + 2, A + 4), 0x2001] + bl(A + 6, B) +
                                             [branch(A + 10, A + 4)], "fall straight through"),
            "pop in the prefix": ([0xB510, 0xBC10, 0x2001] + bl(A + 6, B) + [branch(A + 10, A + 4)],
                                  "fall straight through"),
            "conditional closing branch": ([0xB500, 0x2001] + call + [0xD0FB, 0xE7FE], "fall straight through"),
            "indirect transfer in the loop": ([0xB500, 0x4708] + call + close, "indirect control flow"),
            "pc write in the loop": ([0xB500, 0x468F] + call + close, "program-counter write"),
            "sp write in the loop": ([0xB500, 0x468D] + call + close, "stack-pointer adjustment"),
            "interrupt in the loop": ([0xB500, 0xDF00] + call + close, "interrupts"),
            "call to an unvalidated target": ([0xB500, 0x2001] + bl(A + 4, B + 0x10000) + close,
                                              "validated external direct Thumb BL"),
            # push; cmp r0,#15; beq to the return; bl B; b back to the bl; pop {r0}; bx r0.
            "return path": ([0xB500, 0x280F, 0xD002] + bl(A + 6, B) + [branch(A + 10, A + 6), 0xBC01, 0x4700],
                            "terminal tails must be straight-line"),
        }
        for name, (words, message) in cases.items():
            # Each case has one BL; the validated call at its site is always to B.
            site = A + 2 * next(index for index, word in enumerate(words) if word & 0xF800 == 0xF000)
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message):
                self.walk(words, {site: B})

    def test_forged_loop_manifests_refuse(self):
        records = [None, {"branch": 8, "calls": [4], "head": 4}, {"branch": 6, "calls": [4], "head": 2},
                   {"branch": 8, "calls": [], "head": 2}, {"branch": 8, "calls": [4, 4], "head": 2},
                   {"branch": 8.0, "calls": [4], "head": 2}, {"branch": 8, "calls": (4,), "head": 2},
                   dict(LOOP_RECORD, spins=[]), [2, 8, [4]], {}]
        for record in records:
            manifest = dict(LOOP_MANIFEST, loop=record)
            if record is None:
                del manifest["loop"]
            with self.subTest(record=record), self.assertRaises(ValueError):
                self.verify(body(LOOP), manifest)
        for name, manifest in (("spin", dict(LOOP_MANIFEST, spins=[8])), ("tail", dict(LOOP_MANIFEST, tails=[2])),
                               ("frame", dict(LOOP_MANIFEST, frame=True)),
                               ("unindexed call", dict(LOOP_MANIFEST, calls=[[4, "func_08030000"]]))):
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.verify(body(LOOP), manifest)
        # The loop at the entry has head 0, so a boolean head would compare equal to it.
        entry = body([0x2001] + bl(A + 2, B) + [branch(A + 6, A)])
        manifest = {"calls": [[2, "func_08020000"]], "frame": False, "spins": [],
                     "loop": {"branch": 6, "calls": [2], "head": 0}}
        self.verify(entry, manifest)
        with self.assertRaisesRegex(ValueError, "call-loop record"):
            self.verify(entry, dict(manifest, loop={"branch": 6, "calls": [2], "head": False}))
        # A call at the entry has offset 0, so a boolean call offset would compare equal to it too.
        at_entry = body(bl(A, B) + [branch(A + 4, A)])
        manifest = {"calls": [[0, "func_08020000"]], "frame": False, "spins": [],
                    "loop": {"branch": 4, "calls": [0], "head": 0}}
        self.verify(at_entry, manifest)
        with self.assertRaisesRegex(ValueError, "call-loop record"):
            self.verify(at_entry, dict(manifest, loop={"branch": 4, "calls": [False], "head": 0}))
        # A null loop record is not an absent one: it would state the loop summary on a function that returns.
        with self.assertRaisesRegex(ValueError, "call-loop record"):
            self.verify(body(TAIL), {"calls": [], "frame": False, "spins": [10], "tails": [6, 8], "loop": None})
        # A loop record on a function that returns, and on a self-branch alone.
        with self.assertRaisesRegex(ValueError, "disagrees"):
            self.verify(body(TAIL), {"calls": [], "frame": False, "spins": [10], "tails": [6, 8],
                                     "loop": {"branch": 10, "calls": [], "head": 10}})
        with self.assertRaisesRegex(ValueError, "typed call inside the cycle"):
            self.verify(body([0xB500, 0xE7FE]), {"calls": [], "frame": False, "spins": [],
                                                 "loop": {"branch": 2, "calls": [], "head": 2}})


class CompiledInertSpinTests(unittest.TestCase):
    """Original-ELF provenance, the written report and its fresh replay."""

    def setUp(self):
        scratch = Path(os.environ.get("FFTA_TEST_SCRATCH", Path(__file__).resolve().parents[1] / "build"))
        scratch.mkdir(parents=True, exist_ok=True)
        directory = tempfile.TemporaryDirectory(prefix="inert_spin_", dir=scratch)
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        for name in ("src", "include", "config", "symbols"):
            (self.root / name).mkdir()
        environment = patch.dict(os.environ, {"TMPDIR": str(self.root), "PYTHONDONTWRITEBYTECODE": "1",
                                               "FFTA_ROM": str(self.root / "baserom.bin")})
        environment.start()
        self.addCleanup(environment.stop)
        self.args = argparse.Namespace(cc=match.DEFAULT_CC, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                                       objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD,
                                       flags=match.DEFAULT_FLAGS)

    def fixture(self, source, objects=OBJECTS):
        (self.root / "src/08010000.c").write_text(source)
        (self.root / "config/data_symbols.json").write_text(json.dumps(objects, indent=2) + "\n")
        self.objects = (self.root / "config/data_symbols.json").read_bytes()
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, self.original = match.compile_object(runner, workspace, self.args, self.root, A,
                                                       "src/08010000.c")
            symbol, _ = match.function_record(self.original, "func_08010000", A, True)
            self.mapping, self.index = indexes(symbol["size"])
            self.literals = {}
            self.body, self.calls = profile.object_bytes(
                runner, workspace, self.args, self.original, A, self.mapping, image(b""),
                data_mapping=self.objects, data_relocations=self.literals)
        self.rom = image(self.body)
        for name, data in (("baserom.bin", self.rom), ("config/functions.json", self.mapping),
                           ("symbols/functions.txt", self.index)):
            (self.root / name).write_bytes(data)

    def native_report(self):
        with patch.object(sys, "argv", ["match.py", "--root", str(self.root), "--control-flow-profile",
                                        profile.SELECTOR, "0x08010000"]), \
                patch.object(match, "ROOT", match.ROOT), redirect_stdout(io.StringIO()):
            self.assertEqual(match.main(), 0)
        return (self.root / "docs/match/08010000.md").read_text()

    def manifest(self, report):
        line = next(line for line in report.splitlines() if line.startswith("* inert spin manifest: "))
        return json.loads(line.split("`")[1])

    def replays(self, report):
        return report_fixtures.replay(report, self.root, A)

    def refusal(self):
        with patch.object(sys, "argv", ["match.py", "--root", str(self.root), "--control-flow-profile",
                                        profile.SELECTOR, "--no-write", "0x08010000"]), \
                patch.object(match, "ROOT", match.ROOT), redirect_stdout(io.StringIO()), \
                self.assertRaises(SystemExit) as caught:
            match.main()
        return str(caught.exception.code)

    def rehash(self, report, manifest, altered):
        source = evidence.source_fingerprint(self.root, A)
        return report.replace(profile.manifest_text(manifest), profile.manifest_text(altered)).replace(
            profile.fingerprint(A, self.body, manifest, source, self.mapping, self.index, data_mapping=self.objects),
            profile.fingerprint(A, self.body, altered, source, self.mapping, self.index, data_mapping=self.objects))

    def test_data_with_terminal_tail_matches_and_report_binds_the_data_map(self):
        self.fixture(TAIL_SOURCE)
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual([record[1:] for record in manifest["data"]], [["data_03000100", 0]] * 2)
        self.assertEqual(set(manifest), {"calls", "data", "frame", "spins", "tails"})
        for offset in manifest["spins"]:
            self.assertEqual(self.body[offset:offset + 2], b"\xfe\xe7")
        self.assertEqual(manifest["tails"], list(range(manifest["tails"][0], manifest["spins"][0], 2)))
        self.assertIn(f"* data symbols SHA-256: `{hashlib.sha256(self.objects).hexdigest()}`", report)
        self.assertIn(f"* inert spins: {profile.TAIL_SUMMARY}", report)
        self.assertIn("**MATCH - byte identical**", report)
        self.assertTrue(self.replays(report))

        data_line = f"* data symbols SHA-256: `{hashlib.sha256(self.objects).hexdigest()}`"
        edits = {
            "dropped data line": report.replace(data_line + "\n", ""),
            "duplicated data line": report.replace(data_line, data_line + "\n" + data_line),
            "other data digest": report.replace(data_line, "* data symbols SHA-256: `" + "0" * 64 + "`"),
            "plain summary": report.replace(profile.TAIL_SUMMARY, profile.SUMMARY),
        }
        record = manifest["data"][0]
        for name, changed in (("addend", [record[0], record[1], 4]), ("offset", [record[0] + 4] + record[1:])):
            altered = dict(manifest, data=[changed] + manifest["data"][1:])
            text = report.replace(profile.manifest_text(manifest), profile.manifest_text(altered))
            proof = profile.fingerprint(A, self.body, altered, evidence.source_fingerprint(self.root, A),
                                        self.mapping, self.index, data_mapping=self.objects)
            old = profile.fingerprint(A, self.body, manifest, evidence.source_fingerprint(self.root, A),
                                      self.mapping, self.index, data_mapping=self.objects)
            edits[f"rehashed {name}"] = text.replace(old, proof)
        altered = dict(manifest, data=manifest["data"][:1])
        edits["rehashed dropped record"] = report.replace(profile.manifest_text(manifest),
                                                          profile.manifest_text(altered)).replace(
            profile.fingerprint(A, self.body, manifest, evidence.source_fingerprint(self.root, A),
                                self.mapping, self.index, data_mapping=self.objects),
            profile.fingerprint(A, self.body, altered, evidence.source_fingerprint(self.root, A),
                                self.mapping, self.index, data_mapping=self.objects))
        stripped = {key: value for key, value in manifest.items() if key != "tails"}
        edits["dropped tails"] = report.replace(profile.manifest_text(manifest), profile.manifest_text(stripped))
        for name, changed in edits.items():
            with self.subTest(name=name):
                self.assertNotEqual(changed, report)
                self.assertFalse(self.replays(changed))
        (self.root / "config/data_symbols.json").write_text(json.dumps(dict(OBJECTS, data_03000200="0x03000200")))
        self.assertFalse(self.replays(report))

    def test_signed_addends_match_and_replay(self):
        self.fixture(ADDEND_SOURCE, dict(OBJECTS, data_03000200="0x03000200"))
        self.assertEqual(sorted(self.literals.values()), [("data_03000100", 0x03000110),
                                                          ("data_03000200", 0x030001FC)])
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual(sorted(record[1:] for record in manifest["data"]),
                         [["data_03000100", 16], ["data_03000200", -4]])
        self.assertNotIn("tails", manifest)
        self.assertIn(f"* inert spins: {profile.SUMMARY}", report)
        self.assertTrue(self.replays(report))

    def test_unmapped_object_and_no_opt_in_refuse(self):
        self.fixture(PLAIN_SOURCE)
        (self.root / "src/08010000.c").write_text(TAIL_SOURCE)
        runner = match.Runner(match.DEFAULT_CC, root=self.root, timeout=120)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, self.args, self.root, A, "src/08010000.c")
            symbol, _ = match.function_record(original, "func_08010000", A, True)
            mapping, _ = indexes(symbol["size"])
            for objects in (b"{}", json.dumps({"data_03000200": "0x03000200"}).encode(), None):
                with self.subTest(objects=objects), self.assertRaisesRegex(ValueError, "mapped global object"):
                    profile.object_bytes(runner, workspace, self.args, original, A, mapping, image(b""),
                                         data_mapping=objects, data_relocations={})
            with self.assertRaisesRegex(ValueError, "exclude non-call relocations"):
                profile.object_bytes(runner, workspace, self.args, original, A, mapping, image(b""),
                                     data_mapping=self.objects)
        (self.root / "src/08010000.c").write_text(FUNCTION_SOURCE)
        with runner.workspace() as workspace:
            _, _, original = match.compile_object(runner, workspace, self.args, self.root, A, "src/08010000.c")
            symbol, _ = match.function_record(original, "func_08010000", A, True)
            mapping, _ = indexes(symbol["size"])
            with self.assertRaisesRegex(ValueError, "exclude function-address relocations"):
                profile.object_bytes(runner, workspace, self.args, original, A, mapping, image(b""),
                                     data_mapping=self.objects, data_relocations={})

    def test_call_loop_after_named_data_stores_matches_and_replays(self):
        self.fixture(LOOP_SOURCE)
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual(manifest, {"calls": [[12, "func_08020000"]], "data": [[20, "data_03000100", 0]],
                                    "frame": False, "loop": {"branch": 16, "calls": [12], "head": 12},
                                    "spins": []})
        self.assertEqual(self.body[16:18], struct.pack("<H", branch(A + 16, A + 12)))
        self.assertIn(f"* control flow: {profile.LOOP_CONTROL_FLOW}\n", report)
        self.assertIn(f"* inert spins: {profile.LOOP_SUMMARY}\n", report)
        self.assertIn(f"* data symbols SHA-256: `{hashlib.sha256(self.objects).hexdigest()}`", report)
        self.assertIn("**MATCH - byte identical**", report)
        self.assertTrue(self.replays(report))

        edits = {
            "spin control flow": report.replace(profile.LOOP_CONTROL_FLOW, profile.CONTROL_FLOW),
            "spin summary": report.replace(profile.LOOP_SUMMARY, profile.SUMMARY),
            "tail summary": report.replace(profile.LOOP_SUMMARY, profile.TAIL_SUMMARY),
        }
        loop = manifest["loop"]
        for name, altered in (
                ("dropped loop", {key: value for key, value in manifest.items() if key != "loop"}),
                ("loop as a spin", dict({key: value for key, value in manifest.items() if key != "loop"},
                                        spins=[loop["branch"]])),
                ("other head", dict(manifest, loop=dict(loop, head=loop["head"] - 2))),
                ("no loop calls", dict(manifest, loop=dict(loop, calls=[]))),
                ("extra spin", dict(manifest, spins=[loop["branch"]]))):
            edits[f"rehashed {name}"] = self.rehash(report, manifest, altered)
        for name, changed in edits.items():
            with self.subTest(name=name):
                self.assertNotEqual(changed, report)
                self.assertFalse(self.replays(changed))

        # Changed bytes: the ROM's closing branch now targets the instruction before the call.
        rom = bytearray(self.rom)
        rom[A - match.ROM_BASE + 16:A - match.ROM_BASE + 18] = struct.pack("<H", branch(A + 16, A + 10))
        (self.root / "baserom.bin").write_bytes(bytes(rom))
        self.assertFalse(self.replays(report))
        self.assertIn("differs from ROM", self.refusal())

    def test_framed_call_loop_with_prefix_call_and_stack_reloads_matches(self):
        self.fixture(FRAMED_LOOP_SOURCE)
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual(set(manifest), {"calls", "frame", "loop", "spins"})
        self.assertTrue(manifest["frame"])
        self.assertEqual(manifest["spins"], [])
        loop = manifest["loop"]
        sites = [record[0] for record in manifest["calls"]]
        self.assertEqual(len(sites), 4)
        self.assertLess(sites[0], loop["head"])
        self.assertEqual(loop["calls"], sites[1:])
        self.assertEqual(loop["branch"] + 2, len(self.body))
        self.assertIn("* stack frame:", report)
        self.assertIn(f"* control flow: {profile.LOOP_CONTROL_FLOW}\n", report)
        self.assertNotIn("* data symbols", report)
        self.assertTrue(self.replays(report))

    def test_call_loop_mutants_refuse(self):
        for name, (source, message) in LOOP_REFUSALS.items():
            with self.subTest(name=name):
                self.fixture(source)
                self.assertIn(message, self.refusal())
        indirect = """void func_08010000(void (*callback)(void))
{
    for (;;)
        callback();
}
"""
        unindexed = """extern void func_08030000(void);

void func_08010000(void)
{
    for (;;)
        func_08030000();
}
"""
        for name, source, message in (("indirect call", indirect, "canonical addressed function"),
                                      ("callee outside the index", unindexed, "function address is unknown")):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, message):
                self.fixture(source)

    def test_tail_without_data_and_plain_spin_keep_their_shapes(self):
        self.fixture(PARAMETER_SOURCE)
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual(set(manifest), {"calls", "frame", "spins", "tails"})
        self.assertNotIn("* data symbols", report)
        self.assertTrue(self.replays(report))
        forged = report.replace("* inert spins:", f"* data symbols SHA-256: `{hashlib.sha256(self.objects).hexdigest()}`"
                                "\n* inert spins:")
        self.assertFalse(self.replays(forged))
        self.fixture(PLAIN_SOURCE)
        report = self.native_report()
        manifest = self.manifest(report)
        self.assertEqual(set(manifest), {"calls", "frame", "spins"})
        self.assertIn(f"* inert spins: {profile.SUMMARY}", report)
        self.assertNotIn("* data symbols", report)
        self.assertTrue(self.replays(report))


if __name__ == "__main__":
    unittest.main()
