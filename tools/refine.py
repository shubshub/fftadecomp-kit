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


def bl_targets(rom, a, e):
    """every Thumb BL target inside a function"""
    out = []
    off = a - ROM_BASE
    stop = e - ROM_BASE
    while off + 3 < stop:
        hw = struct.unpack_from("<H", rom, off)[0]
        n = width(rom, off)
        if n == 4:
            hw2 = struct.unpack_from("<H", rom, off + 2)[0]
            if (hw & 0xF800) == 0xF000 and (hw2 & 0xD000) == 0xD000:
                s = (hw >> 10) & 1
                i1 = 1 - (((hw2 >> 13) & 1) ^ s)
                i2 = 1 - (((hw2 >> 11) & 1) ^ s)
                v = ((s << 24) | (i1 << 23) | (i2 << 22) |
                     ((hw & 0x3FF) << 12) | ((hw2 & 0x7FF) << 1))
                if s:
                    v -= 1 << 25
                t = off + 4 + v + ROM_BASE
                if t % 2 == 0 and ROM_BASE <= t < ROM_BASE + len(rom):
                    out.append(t)
        off += n
    return out


def ends_on_conditional_branch(rom, a, e):
    """the signature of a truncated span

    A conditional branch always falls through, so it can never be the end of a
    function.  The scanner that built the index stopped there anyway, which is
    why so many spans were short.  (The other kind of stop - an unconditional
    branch out - is a legitimate end.)
    """
    off = a - ROM_BASE
    last = None
    while off < e - ROM_BASE:
        hw = struct.unpack_from("<H", rom, off)[0]
        n = width(rom, off)
        last = (hw, n)
        off += n
    if last is None:
        return False
    hw, n = last
    if n == 2:
        return (hw & 0xF000) == 0xD000 and (hw & 0x0F00) != 0x0F00
    return (hw & 0xF000) == 0xF000


def extend_to_return(rom, a, end, limit):
    """the end of a function whose span was cut at a conditional branch"""
    off = end - ROM_BASE
    stop = limit - ROM_BASE
    while off < stop:
        hw = struct.unpack_from("<H", rom, off)[0]
        n = width(rom, off)
        off += n
        if n == 2 and (((hw & 0xFF00) == 0xBD00 and (hw & 0x8000)) or
                       (hw & 0xFF87) == 0x4700):
            found = off + ROM_BASE
            # Keep the literal pool with the function - but only if there
            # really is one.  Aligning the end up to four bytes
            # unconditionally swallowed the two bytes of inter-function fill
            # that sit between a function and the next prologue, and 1,209
            # entries carried that fill.  The fill is not part of the ELF
            # symbol either, so the span must not include it.
            def data_like(word):
                return (word == 0 or
                        ROM_BASE <= word < ROM_BASE + len(rom) or
                        0x02000000 <= word < 0x04000000 or
                        0x00010000 <= word < 0x00200000)

            aligned = (found + 3) & ~3
            if aligned != found and aligned + 4 <= limit:
                if data_like(struct.unpack_from("<I", rom, aligned - ROM_BASE)[0]):
                    found = aligned
            while found + 4 <= limit:
                word = struct.unpack_from("<I", rom, found - ROM_BASE)[0]
                if not data_like(word):
                    break
                found += 4
            return found
    return None


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
    from rompath import rom_path
    rom = open(rom_path(repo), "rb").read()

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

    # Callees the index has never seen.  A matched function's call targets
    # are read out of the ROM itself, not out of the report text: the report
    # writes a target as '#0x8007138' - seven digits - and mining the text
    # for 0x08XXXXXX missed exactly the addresses that were missing, which
    # left those functions unverifiable.
    # Every indexed function is scanned, not just the matched ones: a callee
    # that the index has never seen makes its caller unverifiable, and the
    # caller that exposes it may be the very function we are trying to
    # verify - which has no report yet, because it could not be verified.
    leaves = []
    for a in sorted(by_start):
        entry = by_start[a]
        if entry.get("mode") != "thumb":
            continue
        for t in bl_targets(rom, a, int(entry["end"], 16)):
            if t in by_start or t in leaves:
                continue
            e = extent_after_return(rom, t, t + 0x400)
            if e and e > t and has_return(rom, t, e):
                leaves.append(t)

    added = 0
    skipped_overlap = []
    for t in sorted(leaves):
        e = extent_after_return(rom, t, t + 0x400)
        if not e:
            continue
        # the new entry must not sit inside an existing one: some indexed
        # spans are far too large and swallow whole regions, and adding a
        # second entry inside one of them makes call_bindings report the
        # target as ambiguous
        clash = next((x for x in starts if x != t and x < e and
                      int(by_start[x]["end"], 16) > t), None)
        if clash is not None:
            skipped_overlap.append((t, clash))
            continue
        funcs.append({"rom": f"0x{t:08X}", "end": f"0x{e:08X}", "mode": "thumb",
                      "instrs": (e - t) // 2, "kind": "call"})
        starts = sorted(starts + [t])
        by_start[t] = funcs[-1]
        added += 1

    # Spans cut at a conditional branch, repaired from the ROM itself.
    #
    # The report-driven pass above can only fix a function that has a report,
    # and a function that needs a repair often cannot get one - the switch
    # profile, for instance, wants an exact mapped span, and a truncated span
    # is why it has none.  So this pass does not need a report: a conditional
    # branch cannot end a function, so the function ends at the next return.
    extended = 0
    ordered = sorted((int(f["rom"], 16), f) for f in funcs)
    for i, (a, entry) in enumerate(ordered):
        if entry.get("mode") != "thumb":
            continue
        end = int(entry["end"], 16)
        if not ends_on_conditional_branch(rom, a, end):
            continue
        nxt = ordered[i + 1][0] if i + 1 < len(ordered) else end + 0x2000
        limit = min(nxt, end + 0x2000)
        found = extend_to_return(rom, a, end, limit)
        if found is None or found <= end or found > nxt:
            continue
        entry["end"] = f"0x{found:08X}"
        entry["instrs"] = (found - a) // 2
        extended += 1

    # Spans that end on the inter-function fill.  The ROM pads a function out
    # to the next prologue with two zero bytes; the assembler pads with
    # 0x46c0, and the ELF symbol stops at the last instruction either way.
    # The old index included that fill, so 0x08036350 claimed 112 bytes for a
    # 110-byte function and match.py refused it: 'compiled symbol is shorter
    # than the indexed span'.  A span that ends with exactly two zero bytes
    # after a return is carrying the fill, not code.
    trimmed = 0
    for a, entry in by_start.items():
        if entry.get("mode") != "thumb":
            continue
        end = int(entry["end"], 16)
        if end - a < 4:
            continue
        if rom[end - 2 - ROM_BASE:end - ROM_BASE] != b"\x00\x00":
            continue
        # the two bytes before the fill must be a return
        last = None
        off = a - ROM_BASE
        while off < end - ROM_BASE:
            hw = struct.unpack_from("<H", rom, off)[0]
            n = width(rom, off)
            if n == 2 and (((hw & 0xFF00) == 0xBD00 and (hw & 0x8000)) or
                           (hw & 0xFF87) == 0x4700):
                last = off + n + ROM_BASE
            off += n
        if last is None or last != end - 2:
            continue
        entry["end"] = f"0x{last:08X}"
        entry["instrs"] = (last - a) // 2
        trimmed += 1

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
        # every corrected span, whichever pass corrected it: the report-driven
        # one and the conditional-branch extension.  symbols/functions.txt used
        # to get only the first, so a dozen spans were right in
        # config/functions.json and still short in the text file - and
        # match.py reads the text file.
        ends = {f"{a:08X}": (real, a + real) for a, _, real in fixed}
        for a, entry in by_start.items():
            key = f"{a:08X}"
            if key not in ends:
                ends[key] = (int(entry["end"], 16) - a, int(entry["end"], 16))
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

    print(f"refined: {len(fixed)} span(s) corrected from reports, "
          f"{trimmed} trimmed of trailing fill, "
          f"{extended} extended past a conditional branch, "
          f"{added} callee/leaves added, {len(funcs):,} entries")
    for addr, why in skipped:
        print(f"  left alone: {addr} ({why})")
    for addr, clash in skipped_overlap:
        print(f"  left alone: 0x{addr:08X} (it lies inside the span of "
              f"0x{clash:08X}, which is too large)")
    return 0


if __name__ == "__main__":
    sys.exit(main())