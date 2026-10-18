#!/usr/bin/env python3
"""
analyze.py - FFTA (AFXE / GBA) ROM analysis and layout extractor.

This is a from-scratch analysis pass over the base ROM:
  * validates the cartridge header (logo / checksum) and reports anomalies
  * performs recursive-descent disassembly (ARM + Thumb) from the entry point
    and from prologue candidates, producing function boundaries
  * classifies the ROM into code / data / asset regions by coverage + entropy
  * writes config/rom_layout.json, symbols/functions.txt, logs/analysis.txt

Nothing here needs an ARM toolchain: capstone does the decoding.

Usage:  python tools/analyze.py [rom] [repo-root]

       The repo root defaults to the current directory, so this tool can
       be run from a decomp repo that vendors it (see fftadecomp-kit).
"""

import json
import math
import os
import struct
import sys
from collections import Counter, defaultdict

try:
    from capstone import (Cs, CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB,
                          CS_GRP_JUMP, CS_GRP_CALL, CS_GRP_RET)
    from capstone.arm_const import ARM_REG_PC
except ImportError:
    sys.exit("analyze.py needs capstone:  python -m pip install capstone")

ROM_BASE = 0x08000000
HEADER_LEN = 0xC0          # GBA header (logo, title, code, pointer fields)
BLK = 0x400                # 4 KiB granularity for the coverage map

_LOG = []


def repo_root(arg=None):
    """The decomp repo this tool operates on.

    Defaults to the current directory (or $FFTA_ROOT), so the tools can live
    in their own repository - see fftadecomp-kit.
    """
    return os.path.abspath(arg or os.environ.get("FFTA_ROOT") or os.getcwd())


def say(*a):
    line = " ".join(str(x) for x in a)
    print(line, flush=True)
    _LOG.append(line)

NINTENDO_LOGO = bytes.fromhex(
    "24ffae51699aa2213a8341789646332860"
    "47f70908e45ab08d701e7b729f743b9e9c17"
    "6f1f0db1d3e82b9b6c8e01f41d7708e5b613ec"
    "a74c12d28f63d331ec8b306b9786e0ff1c6f"
    "381b6ebcd72a3d95a28f76847268f27ab4a2"
    "63da6910421a54f5097418180772305d74b9"
    "91a9a0216d968c615da542f5330ff1587f07"
    "6f88c0a813c037f2f36d8c5e457c741786a2"
    "cb5d3c390418d43c58b78f871f61136f8fb0"
    "f7088ab7259defe13d4cf39526b521c1004c"
    "653b10450084ff9d2426016f463a00788d31"
    "249cb8e8e8891212000002c4000003840000"
    "0100000000")


# --------------------------------------------------------------------------
# decoding
# --------------------------------------------------------------------------

class Decoder:
    """Word -> decoded instruction, cached (ARM and Thumb share the cache)."""

    def __init__(self, rom):
        self.rom = rom
        self.arm = Cs(CS_ARCH_ARM, CS_MODE_ARM)
        self.thumb = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        for c in (self.arm, self.thumb):
            c.detail = True
            c.skipdata = False
        self.arm_cache = {}
        self.thumb_cache = {}

    def arm_ins(self, off):
        """Decode one ARM word. Returns dict or None if undecodable."""
        w = struct.unpack_from("<I", self.rom, off)[0]
        if w in self.arm_cache:
            return self.arm_cache[w]
        ins = None
        for i in self.arm.disasm(self.rom[off:off + 4], ROM_BASE + off, count=1):
            ins = i
            break
        info = self._describe(ins, w, 4) if ins else None
        self.arm_cache[w] = info
        return info

    def thumb_ins(self, off):
        w = struct.unpack_from("<H", self.rom, off)[0]
        if w in self.thumb_cache:
            return self.thumb_cache[w]
        ins = None
        # four bytes, so 32-bit Thumb-2 encodings decode too
        for i in self.thumb.disasm(self.rom[off:off + 4], ROM_BASE + off, count=1):
            ins = i
            break
        info = self._describe(ins, w, 2) if ins else None
        self.thumb_cache[w] = info
        return info

    @staticmethod
    def _describe(ins, word, size):
        md = ins.mnemonic
        grp = ins.groups
        d = {
            "mn": md,
            "op": ins.op_str,
            "sz": size,
            "cond": ins.cc != 14 and size == 4,   # conditional (ARM only)
            "jump": CS_GRP_JUMP in grp,
            "call": CS_GRP_CALL in grp,
            "ret": CS_GRP_RET in grp,
            "tgt": None,
            "writes_pc": False,
            "wr": (),       # registers written
            "pcldr": None,  # (dest_reg, displacement) for `ldr rX, [pc, #imm]`
            "opreg": None,  # rX for bx/bl rX style transfers
        }
        ops = ins.operands
        if ops and ops[0].type == 2:  # ARM_OP_IMM
            if md.startswith("b"):
                d["tgt"] = ops[0].imm - ROM_BASE
        try:
            reads, writes = ins.regs_access()
            d["wr"] = tuple(writes)
        except Exception:
            pass
        # ldr rX, [pc, #imm]  -> remember the literal so a later bx rX resolves
        if md in ("ldr", "ldr.w") and len(ops) == 2 and ops[0].type == 1 \
                and ops[1].type == 3 and ops[1].mem.base == ARM_REG_PC:
            d["pcldr"] = (ops[0].reg, ops[1].mem.disp)
        if md in ("bx", "bl", "blx") and len(ops) == 1 and ops[0].type == 1:
            d["opreg"] = ops[0].reg
        first_is_pc = bool(ops) and ops[0].type == 1 and ops[0].reg == ARM_REG_PC
        any_pc = any(o.type == 1 and o.reg == ARM_REG_PC for o in ops)
        d["writes_pc"] = first_is_pc or (md.startswith("pop") and any_pc)
        return d


# --------------------------------------------------------------------------
# recursive-descent code discovery
# --------------------------------------------------------------------------

class Analyzer:
    def __init__(self, rom, dec):
        self.rom = rom
        self.dec = dec
        self.n = len(rom)
        # coverage: one byte per 4-byte word (size) or 2-byte halfword (thumb)
        self.arm_seen = bytearray(self.n // 4)
        self.thumb_seen = bytearray(self.n // 2)
        self.covered = bytearray(self.n)   # 0 none, 1 arm, 2 thumb (verified)
        self.reached = bytearray(self.n)   # everything the walker stepped on
        self.functions = {}          # off -> dict
        self.externs = Counter()     # addresses left outside ROM (RAM/BIOS calls)
        self.calls = Counter()       # in-ROM call targets seen so far
        self.entry_targets = set() # where the entry point transfers to
        self.in_entry = False
        self.indirect = 0            # indirect transfers seen
        self.max_func_instr = 4000

    # -- helpers
    def in_rom(self, off, size):
        return 0 <= off and off + size <= self.n

    def prologue_ish(self, off, thumb=False):
        """cheap ARM/Thumb prologue test used to seed candidate functions"""
        if thumb:
            if off & 1 or not self.in_rom(off, 2):
                return False
            w = struct.unpack_from("<H", self.rom, off)[0]
            return (w >> 8) in (0xB4, 0xB5)      # push {rlist[,lr]}
        if not self.in_rom(off, 4):
            return False
        w = struct.unpack_from("<I", self.rom, off)[0]
        if (w & 0x0FFF0000) == 0x092D0000:      # stmdb sp!, {regs...}  (ARM push)
            return True
        if (w & 0x0FFF0000) == 0x09240000:      # stmib sp!, {regs...}
            return True
        if (w & 0x0FFF0000) == 0x052D0000 and (w & 0x4000) and (w & 0x1000):
            return True                         # str lr, [sp, #-imm]!  (single-reg push)
        return False

    # -- traversal -------------------------------------------------------
    def literal(self, off, thumb, disp):
        """value of `ldr rX, [pc, #disp]` at `off`"""
        pc = (off + 4) & ~3 if thumb else off + 8
        a = pc + disp
        if 0 <= a and a + 4 <= self.n:
            return struct.unpack_from("<I", self.rom, a)[0]
        return None

    def traverse(self, start, thumb=False, seed_known=None):
        """Walk from `start` following branches; mode switches on BX/BLX/bit0.

        `ldr rX,[pc,#imm]` is resolved so the common `ldr r1,...; bx r1`
        startup pattern walks into the real code instead of dead-ending.
        returns (instr_count, lo_off, hi_off, ended_by)
        """
        stack = [(start, thumb, seed_known or {})]
        lo = hi = start
        count = 0
        ended = "fallthrough"
        while stack:
            off, thumb, known = stack.pop()
            unit = 2 if thumb else 4
            seen = self.thumb_seen if thumb else self.arm_seen
            while self.in_rom(off, unit):
                idx = off // unit
                if seen[idx]:
                    break
                info = self.dec.thumb_ins(off) if thumb else self.dec.arm_ins(off)
                if info is None:
                    ended = "badinsn"
                    break
                seen[idx] = 1
                count += 1
                lo = min(lo, off)
                hi = max(hi, off + unit)
                for i in range(off, off + unit):
                    self.reached[i] = 2 if thumb else 1

                for r in info["wr"]:
                    known.pop(r, None)
                if info["pcldr"] is not None:
                    reg, disp = info["pcldr"]
                    val = self.literal(off, thumb, disp)
                    if val is not None:
                        known[reg] = val

                tgt = info["tgt"]
                if tgt is None and info["opreg"] is not None:
                    val = known.get(info["opreg"])
                    if val is not None:
                        tgt = val - ROM_BASE

                if tgt is not None and (info["jump"] or info["call"] or info["mn"] in ("bx", "blx")):
                    mn = info["mn"]
                    if mn in ("bx", "blx") and info["opreg"] is not None:
                        tthumb = bool(tgt & 1)   # interworking register branch
                    elif mn == "blx":
                        tthumb = True            # blx <imm> always switches to Thumb
                    else:
                        tthumb = thumb           # b/bl stay in the current mode
                    toff = tgt & ~1
                    if self.in_rom(toff, 2) and not (not tthumb and toff & 3):
                        if info["call"]:
                            self.calls[ROM_BASE + tgt] += 1
                        if self.in_entry:
                            self.entry_targets.add(ROM_BASE + tgt)
                        stack.append((toff, tthumb, {}))
                        if not info["cond"]:
                            ended = "call" if info["call"] else "branch"
                            break
                        off += unit
                        continue
                    if info["call"]:
                        ended = "call-out"
                    else:
                        self.externs[ROM_BASE + toff] += 1
                        ended = "branch-out"
                    if not info["cond"]:
                        break
                    off += unit
                    continue

                if info["writes_pc"]:
                    if info["mn"] in ("bx", "blx", "blxl"):
                        self.indirect += 1
                    ended = "indirect"
                    break
                if info["ret"]:
                    ended = "return"
                    break
                off += unit
        return count, lo, hi, ended

    def linear_body(self, off, thumb, limit=0x400):
        """Length of a straight-line instruction block at `off`.

        Functions found by walking the call graph are only known to start
        somewhere; a linear block keeps their asm assembleable instead of
        sweeping a literal pool in as instructions.
        """
        unit = 2 if thumb else 4
        o = off
        n = 0
        while n < limit and self.in_rom(o, unit):
            info = self.dec.thumb_ins(o) if thumb else self.dec.arm_ins(o)
            if info is None:
                break
            n += 1
            o += unit
            if info["ret"] or (info["jump"] and info["tgt"] is not None) \
                    or info["writes_pc"]:
                break
        return n, o

    def discover(self):
        """Entry point first, then every in-ROM call target, then ARM prologues.

        Call targets are the only trustworthy function starts in this ROM:
        a blind Thumb prologue scan matches ~16k false positives inside the
        4bpp tile data, where the byte pair 0xB5 is just two palette indices.
        """
        self.in_entry = True
        c, lo, hi, end = self.traverse(0xC0)
        self.in_entry = False
        n, stop = self.linear_body(0xC0, thumb=False)
        if c:
            self.functions[0xC0] = {"start": 0xC0, "end": stop, "instrs": n,
                                    "kind": "entry", "mode": "arm", "endby": "call"}
            for i in range(0xC0, stop):
                self.covered[i] = 1
        say(f"  entry 0x080000C0: walk {c} instrs to 0x{hi:X} ({end}); "
            f"body {n} instrs to 0x{stop:X}")

        # ---- pass 2: every in-ROM call target reached from the entry walk is a
        # function; take its straight-line body only (recursing here would
        # walk data-as-code and never terminate)
        added = 0
        for addr in sorted(set(self.calls) | self.entry_targets):
            off = addr - ROM_BASE
            if off < 0 or off >= self.n or off in self.functions:
                continue
            tthumb = bool(addr & 1)
            n, stop = self.linear_body(off, tthumb)
            if n < 2:
                continue
            self.functions[off] = {"start": off, "end": stop, "instrs": n,
                                   "kind": "call", "mode": "thumb" if tthumb else "arm",
                                   "endby": "linear"}
            for i in range(off, stop):
                self.covered[i] = 2 if tthumb else 1
            added += 1
        say(f"  call targets: +{added} functions ({len(self.functions)} total)")

        # ---- pass 3: verified prologue scan, ARM then Thumb
        added = self.scan_arm_functions()
        say(f"  arm prologue pass: +{added} functions ({len(self.functions)} total)")
        added = self.scan_thumb_functions()
        say(f"  thumb prologue pass: +{added} functions ({len(self.functions)} total)")
        return len(self.functions)

    def scan_candidates(self):
        """Every 4-aligned address that begins with an ARM push prologue."""
        return [off for off in range(0, self.n - 4, 4)
                if off >= HEADER_LEN and self.prologue_ish(off, thumb=False)]

    def verify_thumb(self, off, limit=128):
        """Linear-verify a Thumb candidate: push {...lr} ... pop {..,pc}/bx lr.

        Returns (instrs, end_off) or None.  This is what separates real
        functions from the 0xB5xx byte pairs that tile data throws off.

        `pop {r0}; bx r0` is the Thumb interworking return - capstone does not
        flag it as a return, so it is recognised here, otherwise every
        function using that epilogue swallows the next one.
        """
        h = struct.unpack_from("<H", self.rom, off)[0]
        if (h >> 8) != 0xB5:                # must be `push {rlist, lr}`
            return None
        n = 0
        o = off
        prev_pop = False
        while n < limit and self.in_rom(o, 2):
            info = self.dec.thumb_ins(o)
            if info is None:
                return None
            n += 1
            o += 2
            ending = info["ret"] or (info["jump"] and info["tgt"] is not None)
            if info["mn"] == "bx" and prev_pop:
                ending = True
            if info["mn"].startswith("pop"):
                prev_pop = True
            elif info["mn"] != "bx":
                prev_pop = False
            if ending:
                if n >= 5:
                    return n, o
                return None
        return None

    def scan_thumb_functions(self):
        """Find verified Thumb functions across the whole ROM."""
        found = 0
        for off in range(HEADER_LEN, self.n - 2, 2):
            if self.thumb_seen[off // 2]:
                continue
            r = self.verify_thumb(off)
            if r is None:
                continue
            n, end = r
            for o in range(off, end):
                self.covered[o] = 2
            for o in range(off, end, 2):
                self.thumb_seen[o // 2] = 1
            if off not in self.functions:
                self.functions[off] = {"start": off, "end": end, "instrs": n,
                                       "kind": "thumb-prologue", "mode": "thumb",
                                       "endby": "return"}
                found += 1
        return found

    def verify_arm(self, off, limit=128):
        """Same check for ARM push prologues."""
        if not self.prologue_ish(off, thumb=False):
            return None
        n = 0
        o = off
        while n < limit and self.in_rom(o, 4):
            info = self.dec.arm_ins(o)
            if info is None:
                return None
            n += 1
            o += 4
            if info["ret"] or (info["jump"] and info["tgt"] is not None):
                if n >= 5:
                    return n, o
                return None
        return None

    def scan_arm_functions(self):
        found = 0
        for off in range(HEADER_LEN, self.n - 4, 4):
            if self.arm_seen[off // 4]:
                continue
            r = self.verify_arm(off)
            if r is None:
                continue
            n, end = r
            for o in range(off, end, 4):
                self.arm_seen[o // 4] = 1
                self.covered[o:o + 4] = b"\x01\x01\x01\x01"
            if off not in self.functions:
                self.functions[off] = {"start": off, "end": end, "instrs": n,
                                       "kind": "arm-prologue", "mode": "arm",
                                       "endby": "return"}
                found += 1
        return found


# --------------------------------------------------------------------------
# header + segmentation
# --------------------------------------------------------------------------

def header_report(rom):
    rep = {}
    title = rom[0xA0:0xAC]
    rep["title"] = title.rstrip(b"\x00").decode("latin-1")
    rep["game_code"] = rom[0xAC:0xB0].decode("latin-1")
    rep["maker_code"] = rom[0xB0:0xB2].decode("latin-1")
    entry_word = struct.unpack_from("<I", rom, 0)[0]
    rep["entry_word"] = f"{entry_word:08X}"
    if (entry_word >> 24) == 0xEA:
        off = ((entry_word & 0x00FFFFFF) << 2) + 8
        rep["entry"] = f"0x{ROM_BASE + off:08X}"
    else:
        rep["entry"] = None
    logo_ok = rom[0x04:0xA0] == NINTENDO_LOGO
    rep["nintendo_logo_ok"] = logo_ok
    if not logo_ok:
        diff = sum(1 for a, b in zip(rom[0x04:0xA0], NINTENDO_LOGO) if a != b)
        rep["nintendo_logo_diff_bytes"] = diff
    chk = 0
    for b in rom[0xA0:0xBD]:
        chk = (chk - b - 1) & 0xFF
    rep["header_checksum"] = {"computed": f"{chk:02X}", "stored": f"{rom[0xBD]:02X}",
                              "ok": chk == rom[0xBD]}
    return rep


def entropy(b):
    if not b:
        return 0.0
    c = Counter(b)
    n = len(b)
    return -sum((v / n) * math.log2(v / n) for v in c.values())


def coverage_segments(rom, an, min_run=0x40):
    """Split the ROM into runs of arm / thumb / data using the coverage map."""
    n = len(rom)
    kind = an.covered
    segs = []
    start = 0
    cur = kind[0]
    for i in range(1, n):
        k = kind[i]
        if k != cur:
            segs.append([start, i, cur])
            start, cur = i, k
    segs.append([start, n, cur])
    merged = []
    for s, e, k in segs:
        if k == 0 and e - s < 0x200:          # ignore specks of data
            continue
        if merged and merged[-1][2] == k:
            merged[-1][1] = e
        else:
            merged.append([s, e, k])
    return [tuple(m) for m in merged]


def coverage_table(rom, an, step=0x10000):
    """code bytes per 64 KiB, so the real shape of the ROM is visible"""
    say(f"== code coverage per {step // 1024} KiB ==")
    say(f"  {'rom':<12} {'code':>8} {'%':>6}  {'arm':>7} {'thumb':>7}  entropy")
    for start in range(0, len(rom), step):
        chunk = an.covered[start:start + step]
        arm = chunk.count(1)
        thumb = chunk.count(2)
        tot = arm + thumb
        if tot == 0 and rom[start:start + step].count(0) == len(chunk):
            ent = "0.00"
        else:
            ent = f"{entropy(rom[start:start+step]):.2f}"
        bar = "#" * int(60 * tot / step)
        say(f"  0x{ROM_BASE + start:08X} {tot:8,} {100.0*tot/step:5.1f}%  "
            f"{arm:7,} {thumb:7,}  {ent:>6} {bar}")


def classify(rom, s, e, kind):
    """Give a segment a human/technical name from its content."""
    size = e - s
    chunk = rom[s:e]
    ent = entropy(chunk)
    zero = chunk.count(0)
    if size >= 0x1000 and zero > size * 0.995:
        return "padding", ent
    if kind == 1:
        return "code_arm", ent
    if kind == 2:
        return "code_thumb", ent
    if ent > 7.6:
        return "asset_compressed", ent
    if ent < 4.6:
        return "asset_gfx", ent
    return "data", ent


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    here = repo_root(args[1] if len(args) > 1 else None)
    rom_path = args[0] if args else os.path.join(here, "baserom.bin")
    json_path = os.path.join(here, "config", "rom_layout.json")
    txt_path = os.path.join(here, "symbols", "functions.txt")
    log_path = os.path.join(here, "logs", "analysis.txt")

    rom = open(rom_path, "rb").read()
    say(f"rom: {rom_path}  {len(rom)} bytes ({len(rom)/1048576:.1f} MiB)")

    hdr = header_report(rom)
    say("== header ==")
    for k, v in hdr.items():
        say(f"  {k}: {v}")

    dec = Decoder(rom)
    an = Analyzer(rom, dec)
    say("== code discovery ==")
    t0 = os.times()
    accepted = an.discover()
    say(f"  functions accepted: {accepted}")
    say(f"  ARM words covered: {sum(an.arm_seen)} / {len(an.arm_seen)}")
    say(f"  Thumb halfwords covered: {sum(an.thumb_seen)} / {len(an.thumb_seen)}")
    say(f"  code bytes: {sum(1 for v in an.covered if v):,} of {len(rom):,}")

    coverage_table(rom, an)
    segs = coverage_segments(rom, an)
    say("== segments ==")
    out_segs = []
    for s, e, kind in segs:
        name, ent = classify(rom, s, e, kind)
        say(f"  {s:08X}-{e:08X} {e-s:9,} {name:<18} entropy {ent:.2f}")
        out_segs.append({
            "name": name,
            "rom_start": f"0x{ROM_BASE + s:08X}",
            "file_start": f"0x{s:08X}",
            "rom_end": f"0x{ROM_BASE + e:08X}",
            "size": e - s,
            "entropy": round(ent, 3),
            "file": f"files/{name}_{s:08X}.bin",
        })

    funcs = sorted(an.functions.values(), key=lambda f: f["start"])
    os.makedirs(os.path.dirname(txt_path), exist_ok=True)
    with open(txt_path, "w", encoding="utf-8", newline="\n") as f:
        f.write("# FFTA - discovered functions (addr end size instrs)\n")
        for fn in funcs:
            f.write(f"{ROM_BASE + fn['start']:08X} {ROM_BASE + fn['end']:08X} "
                    f"{fn['end'] - fn['start']:6d} {fn['instrs']:5d} {fn['endby']}\n")
    say(f"  wrote {txt_path} ({len(funcs)} functions)")

    layout = {
        "rom": os.path.basename(rom_path),
        "size": len(rom),
        "rom_base": f"0x{ROM_BASE:08X}",
        "header": hdr,
        "stats": {
            "functions": len(funcs),
            "arm_words_covered": int(sum(an.arm_seen)),
            "thumb_halfwords_covered": int(sum(an.thumb_seen)),
            "code_bytes": sum(1 for v in an.covered if v),
            "unique_arm_words": len(dec.arm_cache),
        },
        "segments": out_segs,
    }
    os.makedirs(os.path.dirname(json_path), exist_ok=True)
    with open(json_path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(layout, f, indent=2)
    say(f"  wrote {json_path}")

    # machine-readable outputs the splitter consumes
    runs = []
    s = 0
    cur = an.covered[0]
    for i in range(1, len(rom)):
        if rom and an.covered[i] != cur:
            runs.append([s, i, cur])
            s, cur = i, an.covered[i]
    runs.append([s, len(rom), cur])
    with open(os.path.join(here, "config", "coverage.json"), "w",
              encoding="utf-8", newline="\n") as f:
        json.dump(runs, f)
    with open(os.path.join(here, "config", "functions.json"), "w",
              encoding="utf-8", newline="\n") as f:
        json.dump([{
            "rom": f"0x{ROM_BASE + fn['start']:08X}",
            "end": f"0x{ROM_BASE + fn['end']:08X}",
            "mode": fn.get("mode", "arm"),
            "instrs": fn["instrs"],
            "kind": fn["kind"],
        } for fn in funcs], f, indent=1)
    say("  wrote config/coverage.json, config/functions.json")

    os.makedirs(os.path.dirname(log_path), exist_ok=True)
    with open(log_path, "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(_LOG) + "\n")


if __name__ == "__main__":
    main()