"""Repair function spans that the prologue scanner cut short.

The bug this fixes: the original index stopped a function at a *conditional*
branch.  A conditional branch always falls through, so it can never be a
function end - the scanner was reading 'branch to a shared epilogue' as a
boundary.  Seven spans were confirmed cut this way, each of them in the middle
of its own body (0x0802B3D4 48->92, 0x08136028 48->92, 0x0809209C 18->32,
0x080920BC 12->18, 0x0813EF4C 64->142, 0x080C17C8 236->344,
0x08030088 56->224), and all of them surfaced because an agent's source did
not fit the window it was handed.

This is deliberately a repair, not a rebuild.  It:
  * extends an entry only when that entry does not already end in a return;
  * bounds the walk by the next entry's start - starts were right in every
    confirmed case, only ends were wrong;
  * never shrinks anything, because a shrink means we lost a return, which is
    a bug in the walker rather than a correction;
  * skips ARM entries entirely, and never invents entries.

A wholesale rebuild - adding the ~4,200 unindexed call targets and ~4,000 data
pointers as new entries - is a separate job.  It needs ARM/Thumb arbitration
and overlap proofs before it can be trusted; report it, do not write it.

    python tools/index.py --root ../fftadecomp        # report (default)
    python tools/index.py --root ../fftadecomp --apply
"""
import argparse
import json
import os
import struct
import sys

ROM_BASE = 0x08000000
MAX_EXTENSION = 0x2000          # a body this long is almost certainly not one


def insn_width(rom, off):
    hw = struct.unpack_from("<H", rom, off)[0]
    if (hw & 0xF800) in (0xE800, 0xF000, 0xF800) and off + 3 < len(rom):
        return 4
    return 2


def is_return(hw, n):
    if n == 4:
        return False
    if (hw & 0xFF00) == 0xBD00 and (hw & 0x8000):     # pop {..., pc}
        return True
    if (hw & 0xFF87) == 0x4700:                        # bx lr / bx pc
        return True
    return False


def is_data_word(rom, at):
    word = struct.unpack_from("<I", rom, at - ROM_BASE)[0]
    return (word == 0 or ROM_BASE <= word < ROM_BASE + len(rom) or
            0x02000000 <= word < 0x04000000 or
            0x00010000 <= word < 0x00200000)


def ends_with_return(rom, start, end):
    """Complete means: a return, then only literal-pool words.

    Most entries end in a pool, so testing only the final instruction reports
    almost every one of them as cut short.  What matters is whether anything
    that is not pool data follows the last return.
    """
    off = start - ROM_BASE
    last_return = None
    while off < end - ROM_BASE:
        n = insn_width(rom, off)
        if is_return(struct.unpack_from("<H", rom, off)[0], n):
            last_return = off + n
        off += n
    if last_return is None:
        return False
    tail = last_return
    while tail % 4 and tail < end - ROM_BASE:
        tail += 2
    while tail + 4 <= end - ROM_BASE:
        if not is_data_word(rom, tail + ROM_BASE):
            return False
        tail += 4
    return tail >= end - ROM_BASE or (end - ROM_BASE - tail) < 2


def find_return(rom, start, limit):
    """first return at or after `start`, scanning forward linearly"""
    off = start - ROM_BASE
    stop = limit - ROM_BASE
    while off < stop and off < len(rom) - 1:
        n = insn_width(rom, off)
        hw = struct.unpack_from("<H", rom, off)[0]
        if is_return(hw, n):
            return off + n + ROM_BASE
        off += n
    return None


def pool_after(rom, code_end, limit):
    """word-aligned literal words straight after the last instruction"""
    end = code_end
    while end % 4 and end < limit:
        end += 2
    while end + 4 <= limit:
        word = struct.unpack_from("<I", rom, end - ROM_BASE)[0]
        data_like = (word == 0 or ROM_BASE <= word < ROM_BASE + len(rom) or
                     0x02000000 <= word < 0x04000000 or
                     0x00010000 <= word < 0x00200000)
        if not data_like:
            break
        end += 4
    return end


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.environ.get("FFTA_ROOT", "../fftadecomp"))
    ap.add_argument("--report", action="store_true",
                    help="explicitly do nothing; this is the default")
    ap.add_argument("--apply", action="store_true")
    a = ap.parse_args()

    root = os.path.abspath(a.root)
    rom = open(os.path.join(root, "baserom.bin"), "rb").read()
    cfg_path = os.path.join(root, "config", "functions.json")
    funcs = json.load(open(cfg_path))
    by_start = {int(f["rom"], 16): f for f in funcs}
    starts = sorted(by_start)

    complete, cut, unresolved, skipped = 0, [], [], 0
    for i, start in enumerate(starts):
        f = by_start[start]
        end = int(f["end"], 16)
        if f.get("mode") != "thumb":
            skipped += 1
            continue
        if ends_with_return(rom, start, end):
            complete += 1
            continue
        nxt = starts[i + 1] if i + 1 < len(starts) else end + MAX_EXTENSION
        limit = min(nxt, start + MAX_EXTENSION)
        found = find_return(rom, end, limit)
        if found is None or found <= end:
            unresolved.append((start, end, nxt))
            continue
        new_end = pool_after(rom, found, min(limit, nxt))
        cut.append((start, end, min(new_end, nxt)))

    print(f"entries                     {len(funcs):,}")
    print(f"  already end in a return    {complete:,}")
    print(f"  cut short, repairable      {len(cut)}")
    print(f"  cut short, no return found {len(unresolved)}")
    print(f"  skipped (not Thumb)        {skipped}")
    print(f"\nrepairable bytes: "
          f"+{sum(n - o for _, o, n in cut):,}")

    print("\nrepairs:")
    for start, o, n in sorted(cut, key=lambda x: x[0]):
        star = " *" if os.path.exists(os.path.join(root, "src",
                                                  f"{start:08X}.c")) else ""
        print(f"  0x{start:08X}  0x{o:08X} -> 0x{n:08X}  "
              f"+{n - o}{star}")
    print("  (* already has a matched source)")

    if unresolved:
        print("\nno return found before the next entry - left alone:")
        for start, end, nxt in unresolved[:10]:
            print(f"  0x{start:08X}  ends 0x{end:08X}, next entry 0x{nxt:08X}")

    matched = [s for s, _, _ in cut
               if os.path.exists(os.path.join(root, "src", f"{s:08X}.c"))]
    if matched:
        print("\nWARNING: repairs touch matched functions:",
              ", ".join(f"0x{s:08X}" for s in matched))

    if not a.apply:
        print("\nreport only - nothing written.")
        return

    for start, o, n in cut:
        f = by_start[start]
        f["end"] = f"0x{n:08X}"
        f["instrs"] = (n - start) // 2

    problems = []
    for i in range(len(funcs) - 1):
        e0 = int(funcs[i]["end"], 16)
        a1 = int(funcs[i + 1]["rom"], 16)
        if a1 < e0:
            problems.append((int(funcs[i]["rom"], 16), e0, a1))
    if problems:
        sys.exit(f"refusing to write: {len(problems)} overlaps, first "
                 f"0x{problems[0][0]:08X}-0x{problems[0][1]:08X} contains "
                 f"0x{problems[0][2]:08X}")

    with open(cfg_path, "w", encoding="utf-8", newline="\n") as fh:
        json.dump(funcs, fh, indent=2)
        fh.write("\n")
    print(f"\nrewrote {len(funcs):,} entries ({len(cut)} repaired)")
    print("NOTE: linked match reports bind against this mapping; re-run")
    print("      status.py --verify afterwards.")


if __name__ == "__main__":
    main()
