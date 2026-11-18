"""Original scaled polygon, independent row interpolation and native proof boundaries."""

import argparse
import copy
import json
import os
from pathlib import Path
import struct
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import match
import match_evidence
import owner_admission_profile as owner
import scaled_polygon as polygon

BASE = match.ROM_BASE
P, S, OUT, STATE, TASK = 0x02010000, 0x02011000, 0x02012000, 0x02013000, 0x02014000
SP, STOP = 0x03007A00, 0x080000C0
BIAS = 0x02009160


def s16(x):
    return ((x + 32768) & 65535) - 32768


def oracle(points, offsets, mode, scale, bias, initial):
    """Closed-form half-step rounding, sorting endpoints by row for each edge."""
    n = len(points)
    low = min(range(n), key=lambda i: points[i][1])
    high = max(range(n), key=lambda i: points[i][1])
    next_i = (low + 1) % n
    ax, ay = points[low]
    bx, by = points[next_i]
    cx, cy = points[(high + (high == next_i)) % n]
    direction = (bx - ax) * (cy - ay) >= (by - ay) * (cx - ax)

    def transform(v, center, factor):
        return s16(center + (s16(v) - center) * factor // 256)

    def xy(x, y):
        return transform(x, scale[0], scale[2]), transform(y, scale[1], scale[3])

    first_x, first_y = xy(ax, ay)
    y_base = 0 if mode else first_y
    corners = [(first_x, first_y - y_base)]
    for i in range(1, n):
        x, y = points[((low + i) & 65535) % n]
        corners.append(xy(x + offsets[0], y + offsets[1] - y_base))
    rows = [list(initial) for _ in range(160)]
    calls = []
    for (x0, y0), (x1, y1) in zip(corners, corners[1:] + corners[:1]):
        side = int(direction == (y0 < y1))
        calls.append((polygon.RIGHT if side else polygon.LEFT, x0, y0, x1, y1))
        if y0 == y1:
            if 0 <= y0 < 160:
                rows[y0] = [min(x0, x1) & 65535, max(x0, x1) & 65535]
            continue
        if y0 > y1:
            x0, x1, y0, y1 = x1, x0, y1, y0
        height = y1 - y0
        threshold = height // 2
        rounding = height - threshold if threshold else 0
        for y in range(max(y0, 0), min(y1, 160)):
            dx = ((y - y0) * abs(x1 - x0) + rounding) // height
            x = x0 + (dx if x1 >= x0 else -dx)
            rows[y][side] = (x + (bias if side else 0)) & 65535
    return low, calls, b"".join(struct.pack("<HH", *r) for r in rows)


class Machine:
    def __init__(self, rom, scratch):
        import unicorn as uc
        from unicorn import arm_const as arm

        self.arm, self.scratch = arm, scratch
        self.regs = (arm.UC_ARM_REG_R0, arm.UC_ARM_REG_R1, arm.UC_ARM_REG_R2, arm.UC_ARM_REG_R3)
        self.u = u = uc.Uc(uc.UC_ARCH_ARM, uc.UC_MODE_THUMB)
        u.mem_map(BASE + 0x7000, 0x9000)
        u.mem_write(BASE + 0x7000, rom[0x7000:0x10000])
        u.mem_map(BASE + 0x10000, 0x1000)
        u.mem_write(BASE + 0x10000, rom[0x10000:0x11000])
        u.mem_map(0x08141000, 0x1000)
        u.mem_write(0x08141000, rom[0x141000:0x142000])
        u.mem_map(0x02000000, 0x40000)
        u.mem_map(0x03000000, 0x8000)
        u.mem_map(BASE, 0x1000)
        u.hook_add(uc.UC_HOOK_INTR, self.service)
        for pc in (polygon.LEFT, polygon.RIGHT, polygon.WINDING, 0x0800DF2A, polygon.OWNER):
            u.hook_add(uc.UC_HOOK_CODE, self.observe, begin=pc, end=pc)
        self.edges, self.minima, self.entries = [], [], []
        self.formal = None

    def args(self):
        return tuple(self.u.reg_read(r) for r in self.regs)

    def service(self, u, number, _):
        pc = u.reg_read(self.arm.UC_ARM_REG_PC)
        assert pc == 0x08141876 and bytes(u.mem_read(pc - 2, 2)) == b"\x06\xdf"
        numerator, denominator, _, _ = self.args()
        if not denominator:
            raise ZeroDivisionError("original BIOS service 6 received denominator zero")
        q, r = divmod(numerator, denominator)
        u.reg_write(self.regs[0], q)
        u.reg_write(self.regs[1], r)
        if self.scratch:
            u.reg_write(self.regs[2], 0xC871FFAB)
            u.reg_write(self.regs[3], abs(q))

    def observe(self, u, pc, size, _):
        regs = self.args()
        sp = u.reg_read(self.arm.UC_ARM_REG_SP)
        if pc == polygon.OWNER:
            self.owner_sp = sp
            self.entries.append((regs, struct.unpack("<III", u.mem_read(sp, 12))))
        elif pc == polygon.WINDING:
            self.formal = regs[2]
            assert self.formal == self.owner_sp - 72 + 4
        elif pc == 0x0800DF2A:
            assert self.formal == regs[1]
            self.minima.append(regs[2])
        else:
            self.edges.append((pc, *(s16(n) for n in regs)))
            assert bytes(u.mem_read(sp, 4)) == struct.pack("<I", self.output)

    def run(self, address, points, offsets, mode, scale, bias, frame=0):
        u = self.u
        self.edges.clear()
        self.minima.clear()
        self.entries.clear()
        self.formal = None
        count = len(points)
        packed = b"".join(struct.pack("<hh", *p) for p in points)
        u.mem_write(BIAS, bytes([bias]))
        if address in (0x0800E110, 0x0800E1A0):
            self.output = STATE + 8
            u.mem_write(STATE, bytes(0x298))
            u.mem_write(STATE, struct.pack("<hhHH", *offsets, 0, 4))
            u.mem_write(STATE + 0x288, struct.pack("<IH", P, frame))
            u.mem_write(STATE + 0x290, struct.pack("<hhhh", *scale))
            u.mem_write(P, struct.pack("<HH", count, 2) + packed * 2)
            u.mem_write(TASK + 0x10, struct.pack("<H2xI", 1, STATE))
            args = (STATE if address == 0x0800E1A0 else TASK,)
            initial = (245, 250)
        else:
            self.output = OUT
            initial = (234, 252)
            u.mem_write(P, packed)
            u.mem_write(S, struct.pack("<hhhh", *scale))
            u.mem_write(OUT - 8, b"REDZONE!" + struct.pack("<HH", *initial) * 160 + b"REDZONE!")
            args = (P, count, *offsets, OUT, mode, S)
        for r, n in zip(self.regs, args):
            u.reg_write(r, n & 0xFFFFFFFF)
        for i, n in enumerate(args[4:]):
            u.mem_write(SP + i * 4, struct.pack("<I", n))
        u.reg_write(self.arm.UC_ARM_REG_SP, SP)
        u.reg_write(self.arm.UC_ARM_REG_LR, STOP | 1)
        u.emu_start(address | 1, STOP, count=1200000)
        assert u.reg_read(self.arm.UC_ARM_REG_PC) == STOP and u.reg_read(self.arm.UC_ARM_REG_SP) == SP
        if address in (0x0800E110, 0x0800E1A0):
            assert self.entries == [
                (
                    (P + 4 + frame * count * 4, count, offsets[0] & 0xFFFFFFFF, offsets[1] & 0xFFFFFFFF),
                    (self.output, 1, STATE + 0x290),
                )
            ]
            assert bytes(u.mem_read(P + 4, 2 * len(packed))) == packed * 2
        else:
            assert bytes(u.mem_read(OUT - 8, 8)) == bytes(u.mem_read(OUT + 640, 8)) == b"REDZONE!"
            assert bytes(u.mem_read(P, len(packed))) == packed
        low, edges, expected = oracle(points, offsets, mode, scale, bias, initial)
        assert self.minima == [low] and self.edges == edges
        assert bytes(u.mem_read(self.output, 640)) == expected


class ScratchLifetime(unittest.TestCase):
    def probe(self, code):
        decoder = match.Cs(match.CS_ARCH_ARM, match.CS_MODE_THUMB)
        decoder.detail = True
        address = polygon.REMAINDER + 4
        items = {i.address: i for i in decoder.disasm(bytes.fromhex(code), address)}
        proof = object.__new__(polygon.PolygonProof)
        proof.ins = items
        proof.edges = {pc: ((pc + ins.size,) if pc + ins.size in items else ()) for pc, ins in items.items()}
        proof.calls = {}
        return proof, address

    def test_first_overwrite_and_first_read_are_distinct(self):
        proof, site = self.probe("019a02bc1047")  # LDR r2,[sp,#4]
        self.assertEqual(proof.killed(site, match.ARM_REG_R2), (site,))
        proof, site = self.probe("1068019a1047")  # LDR r0,[r2] first
        self.assertFalse(proof.killed(site, match.ARM_REG_R2))

    def test_call_return_and_backedge_before_kill_refuse(self):
        proof, site = self.probe("c046019a7047")
        proof.calls[site] = polygon.LEFT
        self.assertFalse(proof.killed(site, match.ARM_REG_R2))
        proof.calls = {}
        proof.edges[site] = (site,)
        self.assertFalse(proof.killed(site, match.ARM_REG_R2))
        proof.edges[site] = ()
        self.assertFalse(proof.killed(site, match.ARM_REG_R2))


class Geometry(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        fixture = os.environ.get("FFTA_SCALED_POLYGON_FIXTURE")
        if not fixture:
            raise unittest.SkipTest("FFTA_SCALED_POLYGON_FIXTURE provides the USA ROM/maps and source")
        cls.root = Path(fixture).resolve()
        cls.rom = (cls.root / "baserom.bin").read_bytes()
        cls.mapping, cls.index, cls.objects = (
            match.mapping_snapshot(cls.root),
            (cls.root / "symbols/functions.txt").read_bytes(),
            match.data_snapshot(cls.root),
        )
        cls.bindings = dict(
            calls=[
                [pc - polygon.OWNER, f"func_{target:08X}"] for pc, target in polygon.EXPECTED_CALLS.items()
            ],
            data=[],
            functions=[],
            switches=[],
        )
        cls.body = cls.rom[polygon.OWNER - BASE : polygon.END - BASE]

    def test_original_rotations_windings_ties_clipping_and_scale(self):
        samples = [
            ([(9, 2), (2, 10), (13, 14)], (0, 0), (0, 0, 256, 256), 1),
            ([(-7, -3), (14, -3), (14, 7), (-7, 7)], (2, -1), (3, 2, 192, 320), 1),
            ([(1, 140), (12, 147), (10, 163), (-4, 172), (-9, 151)], (1, 0), (-2, 144, -256, 384), 1),
            ([(0, 4), (15, 13), (8, 20), (-8, 17), (-12, 9)], (-3, 5), (1, 4, 384, -192), 0),
            ([(0, 0), (2, 0), (2, 8), (0, 8)], (0, 0), (0, 0, 0, 256), 1),
            ([(10, 0), (20, 0), (17, 12), (0, 12)], (0, 0), (4, 159, 256, 0), 1),
            ([(5, 1)], (3, 2), (4, 2, 256, 256), 1),
            ([(-10, 2), (10, 10)], (0, 0), (0, 0, 256, 256), 0),
        ]
        for scratch in (False, True):
            cpu = Machine(self.rom, scratch)
            for points, offsets, scale, mode in samples:
                for pts in (points, points[::-1]):
                    for i in range(len(pts)):
                        with self.subTest(scratch=scratch, points=pts, first=i):
                            cpu.run(polygon.OWNER, pts[i:] + pts[:i], offsets, mode, scale, i % 3)
            with self.assertRaises(ZeroDivisionError):
                cpu.run(polygon.OWNER, [], (0, 0), 1, (0, 0, 256, 256), 0)

    def test_two_actual_frame_producers_and_nonzero_frame_offset(self):
        cpu = Machine(self.rom, True)
        for target in (0x0800E110, 0x0800E1A0):
            for frame in (0, 1):
                cpu.run(target, [(-5, -2), (11, 4), (9, 11), (1, 8)], (-2, 3), 1, (4, 0, 192, 320), 1, frame)

    def test_native_proof_replay_and_tampered_manifest(self):
        report = (self.root / "docs/match/0800F480.md").read_text()
        self.assertTrue(match_evidence.report_matches(report, self.root, polygon.OWNER))
        evidence = next(
            line.split("`")[1] for line in report.splitlines() if line.startswith("* owner runtime evidence:")
        )
        manifest = json.loads(evidence)["manifest"]
        private = manifest["proof"]["buffers"]["scaled_polygon"]
        self.assertEqual(len(private["edges"]), 2)
        self.assertTrue(private["mode_join"] and private["root_bios"])
        changed = copy.deepcopy(manifest)
        changed["proof"]["buffers"]["scaled_polygon"]["mode_join"] = []
        with self.assertRaisesRegex(ValueError, "manifest differs"):
            owner.verify(
                self.body,
                polygon.OWNER,
                self.rom,
                self.mapping,
                self.index,
                self.objects,
                manifest=changed,
                bindings=self.bindings,
                selector=polygon.formal.BIOS_SELECTOR,
            )

    def test_original_elf_extent_tail_and_closed_selector(self):
        args = argparse.Namespace(
            cc=match.DEFAULT_CC,
            cpp=match.DEFAULT_CPP,
            assembler=match.DEFAULT_AS,
            linker=match.DEFAULT_LD,
            flags=match.DEFAULT_FLAGS,
            objcopy=match.DEFAULT_OBJCOPY,
        )
        runner = match.Runner(args.cc, "Ubuntu", match.DEFAULT_WSL_PATH, root=str(self.root))
        with runner.workspace() as workspace:
            _, _, image = match.compile_object(
                runner, workspace, args, str(self.root), polygon.OWNER, "src/0800F480.c"
            )

        def bindings(obj, selector):
            return owner.original_bindings(
                obj, polygon.OWNER, self.rom, self.mapping, self.objects, index=self.index, selector=selector
            )

        self.assertEqual(bindings(image, polygon.formal.BIOS_SELECTOR)[0], self.bindings)
        with self.assertRaisesRegex(ValueError, "sole complete"):
            bindings(image, polygon.formal.SELECTOR)
        for change in ("missing", "different", "extended", "owned", "relocation"):
            obj = copy.deepcopy(image)
            if change == "missing":
                obj["text"] = obj["text"][:-2]
            elif change == "different":
                obj["text"] = obj["text"][:-2] + bytes(2)
            elif change == "extended":
                symbol, _ = match.function_record(obj, "func_0800F480", polygon.OWNER, True)
                symbol["size"] += 2
            elif change == "owned":
                obj["symbols"].append(
                    dict(name="owned_tail", value=550, size=2, type=0, bind=1, section=obj["text_index"])
                )
            else:
                section = next(iter(obj["relocations"]))
                raw = obj["section_data"][section]
                obj["section_data"][section] = struct.pack("<I", 550) + raw[4:]
            with self.subTest(change=change), self.assertRaises(ValueError):
                bindings(obj, polygon.formal.BIOS_SELECTOR)

    def test_changed_component_index_or_neighbour_boundary_refuses(self):
        with self.assertRaisesRegex(ValueError, "component"):
            polygon.rom_alignment(
                self.rom,
                self.mapping,
                self.index.replace(b"0800DFB0 0800E05A   170  82", b"0800DFB0 0800E05A   170  85"),
            )
        with self.assertRaisesRegex(ValueError, "padding"):
            polygon.rom_alignment(
                self.rom, self.mapping, self.index.replace(b"0800F6A8 0800F770", b"0800F6A6 0800F770")
            )

    def test_changed_helper_wrapper_edge_caller_and_gap_refuse(self):
        for pc in (0x0800DF2A, 0x08141874, 0x0800E01C, 0x080076A0, 0x0800E20A, polygon.END):
            with self.subTest(pc=pc), self.assertRaises(ValueError):
                changed = bytearray(self.rom)
                changed[pc - BASE] ^= 1
                owner.verify(
                    self.body,
                    polygon.OWNER,
                    bytes(changed),
                    self.mapping,
                    self.index,
                    self.objects,
                    bindings=self.bindings,
                    selector=polygon.formal.BIOS_SELECTOR,
                )


if __name__ == "__main__":
    unittest.main()
