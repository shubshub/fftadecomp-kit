"""Exercise the original combat effect callback, ordinary scene actors, and map queries."""

from pathlib import Path
import struct
from collections import Counter
import os
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import owner_admission_profile as owner
import named_data_buffer_profile as buffers
import match_evidence
from rompath import rom_path
import action_coordinate_query as coordinates

BASE = 0x08000000
SCENE, LIST, ACTION, COMMAND = 0x02001000, 0x02001500, 0x0200F3F0, 0x02001800
SOURCE, TARGET, RELATED, RESULT = 0x02002000, 0x02002200, 0x02002400, 0x02002600
NODES, OBJECTS, ACTORS = 0x02003000, 0x02004000, 0x02006000
GRID = 0x02010000
SP = 0x03005000


def run(rom, count=0, disabled=False, blocked=False, occupied=False, related=False):
    from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB, UC_HOOK_CODE
    from unicorn.arm_const import UC_ARM_REG_R2, UC_ARM_REG_R4, UC_ARM_REG_PC, UC_ARM_REG_SP, UC_ARM_REG_LR

    u = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    u.mem_map(BASE, len(rom))
    u.mem_write(BASE, rom)
    u.mem_map(0x02000000, 0x40000)
    u.mem_map(0x03000000, 0x8000)

    def w(a, v):
        u.mem_write(a, struct.pack("<I", v))

    def b(a, v):
        u.mem_write(a, bytes([v]))

    w(0x0200F4B0, SCENE)
    w(SCENE + 0x10, LIST)
    w(ACTION, SOURCE)
    w(ACTION + 4, TARGET)
    w(ACTION + 8, RESULT)
    w(ACTION + 0x30, COMMAND)
    b(COMMAND + 1, 26)
    u.mem_write(ACTION + 0x26, struct.pack("<H", 0x10 if disabled else 0))
    u.mem_write(RESULT + 0xF6, b"\xfe\xfe")
    for a, x, y in [(SOURCE, 7, 8), (TARGET, 8, 8), (RELATED, 8, 9)]:
        u.mem_write(a + 0xF6, bytes([x, y]))
        b(a + 0x3D, 1)
    if blocked:
        b(TARGET + 0xEA, 8)
    w(0x02007F14, GRID)
    b(0x02007F18, 16)
    b(0x02007F1D, 16)
    b(0x02007F1F, 16)
    u.mem_write(GRID, b"\x01\x00" * 256)
    w(LIST + 4, NODES if count else 0)
    for i in range(count):
        node = NODES + i * 16
        obj = OBJECTS + i * 0x80
        actor = TARGET if i == 0 else ACTORS + i * 0x200
        w(node, obj)
        w(node + 8, node + 16 if i + 1 < count else 0)
        w(obj, actor)
        w(obj + 4, RELATED if related and i == 0 else 0)
        u.mem_write(obj + 0x5C, struct.pack("<H", 0x400))
        if i:
            u.mem_write(
                actor + 0xF6, bytes((9 if occupied and i == 1 else 2, 8 if occupied and i == 1 else 1))
            )
    saved = [ACTION] + [0x11000000 + i for i in range(5, 12)]
    for i, v in enumerate(saved):
        u.reg_write(UC_ARM_REG_R4 + i, v)
    u.reg_write(UC_ARM_REG_LR, BASE | 1)
    u.reg_write(UC_ARM_REG_SP, SP)
    tracker = Counter()
    points = {
        0x08132208,
        0x08098E7C,
        0x08099560,
        0x08099CDC,
        0x08099048,
        0x0809903A,
        0x08132242,
        0x08098EEE,
        0x08098EF2,
        0x08098F1E,
        0x08098F0E,
        0x08098FD8,
        0x08099068,
        0x0812F35A,
        0x0812F35C,
    }
    pointers = {}

    def trace(u, pc, size, _):
        if pc in points:
            tracker[pc] += 1
            pointers.setdefault(pc, u.reg_read(UC_ARM_REG_R2))

    u.hook_add(UC_HOOK_CODE, trace)
    u.emu_start(0x0813388D, 0x081338BE, count=60000)
    assert u.reg_read(UC_ARM_REG_PC) == 0x081338BE, (hex(u.reg_read(UC_ARM_REG_PC)), tracker)
    assert u.reg_read(UC_ARM_REG_SP) == SP - 12
    assert u.reg_read(UC_ARM_REG_R4) == ACTION
    flags = int.from_bytes(u.mem_read(ACTION + 0x26, 2), "little")
    result = tuple(u.mem_read(RESULT + 0xF6, 2))
    u.emu_start(0x081338BF, BASE, count=60000)
    assert u.reg_read(UC_ARM_REG_PC) == BASE
    assert u.reg_read(UC_ARM_REG_SP) == SP
    assert [u.reg_read(UC_ARM_REG_R4 + i) for i in range(8)] == saved
    return flags, result, tracker, pointers


@unittest.skipUnless(os.getenv("FFTA_ACTION_COORDINATE_ROOT"), "requires original USA game and native C")
class ActionCoordinates(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(os.environ["FFTA_ACTION_COORDINATE_ROOT"]).resolve()
        cls.rom = Path(rom_path(cls.root)).read_bytes()
        cls.mapping = match_evidence.mapping_snapshot(cls.root)
        cls.index = (cls.root / "symbols/functions.txt").read_bytes()
        cls.objects = match_evidence.data_snapshot(cls.root)

    def test_original_dispatcher_flag_and_unused_scratch(self):
        flags, result, calls, regs = run(self.rom, disabled=True)
        self.assertEqual((flags, result), (16, (254, 254)))
        self.assertEqual(calls[coordinates.QUERY], 0)
        flags, result, calls, regs = run(self.rom, blocked=True)
        self.assertEqual((flags, result), (0, (254, 254)))
        # Dispatcher saves 12 bytes, callback 28, query 120. Both output
        # bytes remain untouched on this failure, and only the actual next
        # caller consumes the boolean. Its R2 is subsequently overwritten.
        address = SP - 12 - 28 - 120 + 1
        for site in (0x08098EEE, 0x08098EF2, 0x08099068, 0x08132242, 0x0812F35A):
            self.assertEqual(regs[site], address)
        self.assertNotEqual(regs[0x0812F35C], address)

    def test_original_lists_outputs_and_cursor(self):
        for n in range(14):
            with self.subTest(n=n):
                flags, result, calls, regs = run(self.rom, n, related=n % 2)
                self.assertEqual((flags, result), (8, (9, 8)))
                self.assertEqual(calls[0x08099048], 1)
                self.assertEqual(calls[coordinates.GATHER], int(n > 0))
                if n:
                    self.assertEqual(regs[0x08098F1E], SP - 12 - 28 - 120 + 16 + 4 * n)
        flags, result, calls, _ = run(self.rom, 2, occupied=True)
        self.assertEqual((flags, result), (0, (254, 254)))
        self.assertEqual(calls[0x08099048], 0)

    def test_original_reports_and_recorded_scratch(self):
        for name in ("08132208", "0809AA94"):
            path = self.root / "docs/match" / (name + ".md")
            report = path.read_text()
            self.assertTrue(match_evidence.report_matches(report, self.root, int(name, 16)))
        path = self.root / "docs/match/08132208.md"
        report = path.read_text()
        for old, new in [
            ('"capacity":13', '"capacity":14'),
            ('"exact_early_actor_flag_R2":-119', '"exact_early_actor_flag_R2":-118'),
        ]:
            self.assertIn(old, report)
            self.assertFalse(
                match_evidence.report_matches(report.replace(old, new), self.root, coordinates.ROOT)
            )

    def test_wrong_bindings_and_scratch_paths_refuse(self):
        import copy

        data = self.rom[coordinates.ROOT - BASE : coordinates.ROOT - BASE + 96]
        opts = dict(
            data=data,
            address=coordinates.ROOT,
            rom=self.rom,
            mapping=self.mapping,
            index=self.index,
            objects=self.objects,
            selector=buffers.SCRATCH_SELECTOR,
        )
        bindings = copy.deepcopy(coordinates.BINDINGS)
        bindings["calls"][2][1] = "func_08098E7C"
        with self.assertRaises(ValueError):
            owner.verify(**opts, bindings=bindings)
        proof = buffers.DiscardedReturnScratchProof(self.rom, self.mapping, self.index, self.objects)
        with self.assertRaises(ValueError):
            coordinates.verify_call(proof, {coordinates.R0 + 5: -19}, [None] * 7, {-28: -20, -24: -20}, {})
        # Check the frame analyser itself with a changed dependency, independently
        # of the higher-level USA identity gate.
        body, *_ = coordinates.get(proof, coordinates.QUERY)
        altered = bytearray(body)
        altered[0x08099056 - coordinates.QUERY : 0x08099058 - coordinates.QUERY] = bytes.fromhex("001c")
        import owner_graph_profile as graph

        ri, re, _, rc, _ = graph.graph(
            bytes(altered), coordinates.QUERY, owner.refine(bytes(altered), coordinates.QUERY, self.mapping)
        )
        with self.assertRaisesRegex(ValueError, "successful query lacks"):
            coordinates.frame(proof, bytes(altered), ri, re, rc)
        changed = bytearray(self.rom)
        changed[0x0812F35A - BASE : 0x0812F35C - BASE] = bytes.fromhex("101c")
        proof = buffers.DiscardedReturnScratchProof(bytes(changed), self.mapping, self.index, self.objects)
        with self.assertRaisesRegex(ValueError, "uses entry scratch"):
            coordinates.dispatcher_liveness(proof, coordinates.R0 + 2)
