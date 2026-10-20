"""Refine the analysed function index using what the match reports prove.

analyze.py scans for prologues.  That is enough to find a function, but not to
find where it *ends*: a conditional branch always falls through, so the scan
stops a function at a branch that cannot possibly be its end.  Every function
matched so far had a truncated span, one by 8.5x, and the index also never
contains frameless Thumb leaves at all - the scan looks for a prologue, and
those functions have none.

Both faults are repairable, and the repairs are *provable* from things the
repository already holds:

  * the span of a function is whatever the compiled ELF symbol was, and every
    matched function has a report saying so - 'MATCH - byte identical - 92/92
    bytes'.  The report is the authority, and it is committed, so the
    correction is reproducible rather than a hand edit.
  * a frameless leaf is a callee that the index does not have.  The call
    targets of every matched function are known from the reports, and the
    missing ones can be found and given their real extent.

Run after analyze.py, before split.py:

    python tools/refine.py <repo>

It rewrites config/functions.json and symbols/functions.txt in place, and
refuses to write anything it cannot corroborate - a return has to fall inside
the span, and the span must not reach into the next entry.
"""
import json
import os
import re
import struct
import sys

ROM_BASE = 0x08000000


def width(rom, off):
    hw = struct.unpack_from("<H", rom, off)[0]
    return 4 if (hw & 0xF800) in (0xE800, 0xF000, 0xF800) and off + 3 < len(rom) else 2


def has_return(rom, a, e):
    off = a - ROM_BASE
    stop = e - ROM_BASE
    while off < stop:
        hw = struct.unpack_from("<H", rom, off)[0]
        n = width(rom, off)
        if n == 2 and (((hw & 0xFF00) == 0xBD00 and (hw & 0x8000)) or
                       (hw & 0xFF87) == 0x4700):
            return True
        off += n
    return False


def extent_after_return(rom, a, limit):
    """where a frameless leaf ends: its own return"""
    off = a - ROM_BASE
    stop = limit - ROM_BASE
    while off < stop:
        hw = struct.unpack_from("<H", rom, off)[0]
        n = width(rom, off)
        off += n
        if n == 2 and (((hw & 0xFF00) == 0xBD00 and (hw & 0x8000)) or
                       (hw & 0xFF87) == 0x4700):
            return off + ROM_BASE
        if off - (a - ROM_BASE) > 0x400:
            break
    return None


def verified_extents(repo):
    """every address whose true extent a committed report proves"""
    out = {}
    reports = os.path.join(repo, "docs", "match")
    if not os.path.isdir(reports):
        return out
    for name in sorted(os.listdir(reports)):
        if not name.endswith(".md"):
            continue
        text = open(os.path.join(reports, name), encoding="utf-8").read()
        if "MATCH - byte identical" not in text:
            continue
        m = re.search(r"MATCH - byte identical\**\s*-?\s*(\d+)/(\d+) bytes", text)
        if not m or m.group(1) != m.group(2):
            continue
        out[name[:-3]] = int(m.group(1))
    return out


def main():
    repo = os.path.abspath(sys.argv[1] if len(sys.argv) > 1 else ".")
    try:
        from rompath import rom_path
        rom = open(rom_path(repo), "rb").read()
    except ImportError:
        rom = open(os.path.join(repo, "baserom.bin"), "rb").read()

    cfg_path = os.path.join(repo, "config", "functions.json")
    funcs = json.load(open(cfg_path))
    by_start = {int(f["rom"], 16): f for f in funcs}
    starts = sorted(by_start)

    extents = verified_extents(repo)
    fixed, skipped = [], []
    for addr, real in extents.items():
        a = int(addr, 16)
        entry = by_start.get(a)
        if entry is None:
            continue
        old = int(entry["end"], 16) - a
        if old == real:
            continue
        i = starts.index(a)
        nxt = starts[i + 1] if i + 1 < len(starts) else None
        end = a + real
        if not has_return(rom, a, end):
            skipped.append((addr, "no return inside the verified span"))
            continue
        if nxt is not None and end > nxt:
            skipped.append((addr, f"would reach into 0x{nxt:08X}"))
            continue
        entry["end"] = f"0x{end:08X}"
        entry["instrs"] = real // 2
        fixed.append((a, old, real))

    # frameless leaves: a callee the index has never seen
    leaves = []
    for addr in extents:
        a = int(addr, 16)
        entry = by_start.get(a)
        if entry is None:
            continue
        report = os.path.join(repo, "docs", "match", f"{addr}.md")
        text = open(report, encoding="utf-8").read()
        for target in re.findall(r"\b(0x08[0-9A-F]{6})\b", text):
            t = int(target, 16)
            if t in by_start or t in leaves:
                continue
            e = extent_after_return(rom, t, t + 0x400)
            if e and e > t and has_return(rom, t, e):
                leaves.append(t)

    added = 0
    for t in sorted(leaves):
        e = extent_after_return(rom, t, t + 0x400)
        if not e:
            continue
        nxt = next((x for x in starts if x > t), None)
        if nxt and nxt < e:
            continue
        funcs.append({"rom": f"0x{t:08X}", "end": f"0x{e:08X}", "mode": "thumb",
                      "instrs": (e - t) // 2, "kind": "call"})
        starts = sorted(starts + [t])
        added += 1

    funcs.sort(key=lambda f: int(f["rom"], 16))

    overlaps = [(int(funcs[i]["rom"], 16), int(funcs[i]["end"], 16),
                 int(funcs[i + 1]["rom"], 16))
                for i in range(len(funcs) - 1)
                if int(funcs[i + 1]["rom"], 16) < int(funcs[i]["end"], 16)
                and funcs[i].get("mode") == "thumb"]
    if overlaps:
        print(f"refusing to write: {len(overlaps)} Thumb overlap(s), first "
              f"0x{overlaps[0][0]:08X}-0x{overlaps[0][1]:08X} contains "
              f"0x{overlaps[0][2]:08X}")
        return 1

    with open(cfg_path, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(funcs, fh, indent=2)
        fh.write("\n")

    sym = os.path.join(repo, "symbols", "functions.txt")
    if os.path.exists(sym):
        lines = [ln for ln in open(sym, encoding="utf-8").read().splitlines()
                 if ln.split()]
        ends = {f"{a:08X}": (real, a + real) for a, _, real in fixed}
        out = []
        for ln in lines:
            parts = ln.split()
            if parts[0] in ends:
                size, end = ends[parts[0]]
                parts[1] = f"{end:08X}"
                parts[2] = f"{size:>5}"
                parts[3] = f"{size // 2:>3}"
            out.append(" ".join(parts))
        for t in sorted(leaves):
            if any(ln.split()[0] == f"{t:08X}" for ln in out):
                continue
            e = extent_after_return(rom, t, t + 0x400)
            if e:
                out.append(f"{t:08X} {e:08X}     {e - t:>5}    "
                           f"{(e - t) // 2:>3} call")
        out.sort(key=lambda ln: ln.split()[0])
        with open(sym, "w", encoding="utf-8", newline="\n") as fh:
            fh.write("\n".join(out) + "\n")

    print(f"refined: {len(fixed)} span(s) corrected, {added} frameless leaf/leaves "
          f"added, {len(funcs):,} entries")
    for addr, why in skipped:
        print(f"  left alone: {addr} ({why})")
    return 0


if __name__ == "__main__":
    sys.exit(main())