"""Propose a file structure from the ROM.

There are no names and no plaintext in this ROM - every symbol is
func_XXXXXXXX and even 'Knight' is absent, because FFTA stores its text in a
custom encoding.  So the layout has to come out of evidence rather than out of
the binary, and this reads four kinds of it:

  1. shared data bases.  Two functions that reference the same global address
     are working on the same object.  This is the strongest signal we have:
     'Entry', 'ScriptState' and the 0x020101F8 state were all found this way,
     by hand, before this tool existed.  Offsets are not matched literally -
     agbcc puts each field offset in its own pool entry - so the *pointer* is
     what gets shared.

  2. mutual recursion.  A strongly connected component in the call graph is
     almost always one file: you cannot express a cycle across objects without
     prototypes, and a decomp never bothers.

  3. identical code.  Normalised instruction-stream hashes.  0x0802B3D4 and
     0x08136028 are the same function at two addresses, which is proof they
     belong together and, incidentally, a free match for whoever gets there
     second.

  4. the call graph itself, as a weaker hint, and as the thing that reports
     each cluster's cohesion.

Nothing here needs exact function boundaries: clustering on 'these two
functions touch the same global' is unaffected by a span being 20 bytes short.
It reports only.  Naming stays address-based (module_080C.c) until the
semantics are actually recovered, because guessing names is how decompilations
end up with confident, wrong vocabulary.

    python tools/modules.py --root ../fftadecomp
    python tools/modules.py --root ../fftadecomp --out docs/modules.md
"""
import argparse
import json
import os
import struct
from pathlib import Path
from collections import defaultdict

ROM_BASE = 0x08000000
ROM_END = 0x08150000


# ------------------------------------------------------------------ decoding
def insn_width(rom, off):
    hw = struct.unpack_from("<H", rom, off)[0]
    if (hw & 0xF800) in (0xE800, 0xF000, 0xF800) and off + 3 < len(rom):
        return 4
    return 2


def pool_addresses(rom, start, end):
    """values loaded out of the literal pool: every pc-relative ldr"""
    out = set()
    off = start - ROM_BASE
    stop = end - ROM_BASE
    while off + 1 < stop:
        hw = struct.unpack_from("<H", rom, off)[0]
        n = insn_width(rom, off)
        # ldr rX, [pc, #imm]  (Thumb-1)
        if (hw & 0xF800) == 0x4800:
            imm = (hw & 0xFF) * 4
            pool = ((off + 4) & ~3) + imm
            if pool + 3 < len(rom):
                out.add(struct.unpack_from("<I", rom, pool)[0])
        off += n
    return out


def bl_targets(rom, start, end):
    out = set()
    off = start - ROM_BASE
    stop = end - ROM_BASE
    while off + 3 < stop:
        hw = struct.unpack_from("<H", rom, off)[0]
        n = insn_width(rom, off)
        if n == 4:
            hw2 = struct.unpack_from("<H", rom, off + 2)[0]
            if (hw & 0xF800) == 0xF000 and (hw2 & 0xD000) == 0xD000:
                s = (hw >> 10) & 1
                i1 = 1 - (((hw2 >> 13) & 1) ^ s)
                i2 = 1 - (((hw2 >> 11) & 1) ^ s)
                value = ((s << 24) | (i1 << 23) | (i2 << 22) |
                         ((hw & 0x3FF) << 12) | ((hw2 & 0x7FF) << 1))
                if s:
                    value -= 1 << 25
                out.add(off + 4 + value + ROM_BASE)
        off += n
    return out


def code_signature(rom, start, end):
    """hash of the instruction stream, with call targets and pools removed"""
    h = 0
    off = start - ROM_BASE
    stop = end - ROM_BASE
    while off + 1 < stop:
        hw = struct.unpack_from("<H", rom, off)[0]
        n = insn_width(rom, off)
        if n == 4:
            # zero the immediate half of bl / b.w so relocatable twins agree
            h = (h * 31 + (hw & 0xF800)) & 0xFFFFFFFF
        else:
            h = (h * 31 + hw) & 0xFFFFFFFF
        off += n
    return h


# ------------------------------------------------------------------ union-find
class Sets:
    def __init__(self, items):
        self.parent = {i: i for i in items}

    def find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.parent[rb] = ra


def sccs(nodes, edges):
    """Tarjan, iterative"""
    index = {}
    low = {}
    on = set()
    stack = []
    result = []
    counter = [0]
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(edges.get(root, ())))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        on.add(root)
        while work:
            node, it = work[-1]
            advanced = False
            for nxt in it:
                if nxt not in index:
                    index[nxt] = low[nxt] = counter[0]
                    counter[0] += 1
                    stack.append(nxt)
                    on.add(nxt)
                    work.append((nxt, iter(edges.get(nxt, ()))))
                    advanced = True
                    break
                if nxt in on:
                    low[node] = min(low[node], index[nxt])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[node])
            if low[node] == index[node]:
                comp = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    comp.append(w)
                    if w == node:
                        break
                result.append(comp)
    return result


# ------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.environ.get("FFTA_ROOT", "../fftadecomp"))
    ap.add_argument("--out", help="write the report here")
    ap.add_argument("--moves", action="store_true",
                    help="include a git-mv plan for grouped sources")
    ap.add_argument("--min-cluster", type=int, default=2)
    ap.add_argument("--top", type=int, default=40)
    a = ap.parse_args()

    root = os.path.abspath(a.root)
    rom = open(os.path.join(root, "baserom.bin"), "rb").read()
    funcs = json.load(open(os.path.join(root, "config", "functions.json")))
    funcs = [f for f in funcs
             if f.get("mode") == "thumb" and ROM_BASE <= int(f["rom"], 16) < ROM_END]
    matched = {q.stem for q in
               Path(root, "src").rglob("*.c")}

    # A pool word is only evidence of a global if it could *be* one.  Word
    # alignment matters: this ROM is full of small constants (0x54BA and
    # friends) and an odd word like 0x0809ABE9 is an immediate, not a pointer.
    # In the ROM range we additionally require the value to be a real indexed
    # entry or a segment start, so an arbitrary constant cannot masquerade as a
    # code address.
    indexed = {int(f["rom"], 16) for f in funcs}
    segment_starts = set()
    layout_path = os.path.join(root, "config", "rom_layout.json")
    if os.path.exists(layout_path):
        for seg in json.load(open(layout_path))["segments"]:
            segment_starts.add(int(seg["rom_start"], 16))

    def is_global(word):
        if word % 4:
            return False
        if 0x02000000 <= word < 0x04000000:
            return True
        if ROM_BASE <= word < ROM_END:
            return word in indexed or word in segment_starts
        return False

    refs, calls, sigs = {}, {}, defaultdict(list)
    for f in funcs:
        s, e = int(f["rom"], 16), int(f["end"], 16)
        key = s
        pool = {w for w in pool_addresses(rom, s, e) if is_global(w)}
        refs[key] = pool
        calls[key] = {t for t in bl_targets(rom, s, e)
                      if ROM_BASE <= t < ROM_END}
        sigs[code_signature(rom, s, e)].append(key)

    nodes = sorted(refs)
    sets = Sets(nodes)

    # 1. shared data bases
    by_base = defaultdict(list)
    for key in nodes:
        for base in refs[key]:
            by_base[base].append(key)
    MAX_FANOUT = 32
    MAX_CLUSTER = 40
    base_groups = {b: v for b, v in by_base.items() if 1 < len(v) <= MAX_FANOUT}
    anchors = {b: v for b, v in by_base.items() if len(v) > MAX_FANOUT}

    # Merge most-distinctive first and refuse any merge that would over-fill a
    # component.  Plain union-find chains weak links transitively - a dozen
    # globals with four referrers each produce one 'cluster' of hundreds that
    # is not a module - so a global that would blow the cap is demoted to an
    # anchor and reported instead of silently merging.
    sizes = defaultdict(int)
    for n in nodes:
        sizes[sets.find(n)] = 1
    demoted = []
    for base in sorted(base_groups, key=lambda b: len(by_base[b])):
        members = base_groups[base]
        roots = {}
        for m in members:
            r = sets.find(m)
            roots[r] = roots.get(r, 0) + sizes[r]
        if sum(roots.values()) > MAX_CLUSTER:
            demoted.append(base)
            continue
        first = members[0]
        for other in members[1:]:
            sets.union(first, other)
        for r in list(roots):
            sizes[sets.find(r)] = sum(roots.values())
    base_groups = {b: v for b, v in base_groups.items() if b not in demoted}

    # 2. mutual recursion
    edges = {k: {t for t in calls[k] if t in refs} for k in nodes}
    comps = sccs(nodes, edges)
    cycles = [c for c in comps if len(c) > 1]

    # 3. identical code
    # short functions hash alike by accident - thunks and 'bx lr' stubs are
    # not evidence of a shared module
    def size_of(k):
        f = next(x for x in funcs if int(x["rom"], 16) == k)
        return int(f["end"], 16) - k
    twins = [v for v in sigs.values() if len(v) > 1 and size_of(v[0]) >= 16]

    # 4. RAM locality.  The game laid its subsystems out contiguously:
    #    0x0200F370..0x0200F4A8 is 16 globals in 0x140 bytes and all one
    #    subsystem, but shared-global matching alone splits it into four
    #    clusters.  Globals in the same 0x100 page belong together.
    for base in list(base_groups):
        if not 0x02000000 <= base < 0x04000000:
            continue
        page = [b for b in base_groups
                if 0x02000000 <= b < 0x04000000 and b >> 8 == base >> 8]
        if len(page) < 2:
            continue
        anchors = [b for b in page if len(base_groups[b]) >= 3]
        if not anchors:
            continue
        hub = max(anchors, key=lambda b: len(base_groups[b]))
        for b in page:
            for m in base_groups[b]:
                sets.union(base_groups[hub][0], m)

    clusters = defaultdict(list)
    for key in nodes:
        clusters[sets.find(key)].append(key)

    lines = []
    def out(text=""):
        print(text)
        lines.append(text)

    out("# Proposed file structure, derived from the ROM")
    out()
    out(f"    functions considered   {len(nodes):,}")
    out(f"    informative globals   {len(base_groups)} "
        f"(2..{32} referrers), covering "
        f"{len({m for v in base_groups.values() for m in v}):,} functions")
    out(f"    ubiquitous globals    {len(anchors)} (too common to be evidence, "
        f"e.g. the EWRAM base)")
    out(f"    demoted globals       {len(demoted)} (informative alone, but "
        f"merging them would over-fill a cluster)")
    out(f"    mutual-recursion SCCs  {len(cycles)} "
        f"({sum(len(c) for c in cycles)} functions)")
    out(f"    identical-code groups  {len(twins)} "
        f"({sum(len(v) for v in twins)} functions)")
    out()

    multi = sorted((v for v in clusters.values() if len(v) >= a.min_cluster),
                   key=lambda v: -len(v))
    singletons = sum(1 for v in clusters.values() if len(v) == 1)

    out(f"    clusters of >= {a.min_cluster} functions: {len(multi)}")
    out(f"    singletons with no shared evidence: {singletons:,}")
    out()
    out("Names are address-based on purpose. There are no strings in this ROM "
        "to name things")
    out("after, and a wrong confident name is worse than func_080C15DC.")
    out()

    def carve(members, gap=0x100):
        """split addresses into runs that are contiguous in the ROM"""
        runs = []
        for m in sorted(members):
            if runs and m - runs[-1][-1] <= gap:
                runs[-1].append(m)
            else:
                runs.append([m])
        return runs

    out("## Subsystems")
    out()
    out("Memory layout and link order are different things, and keeping them")
    out("apart is the trick.  RAM globals sit in contiguous blocks - one")
    out("subsystem is 0x0200F370..0x0200F4A8 - but a source file lands")
    out("contiguously in the *ROM*, and a subsystem is many files.  So globals")
    out("find the subsystem and ROM contiguity carves the files out of it.")
    out()
    out("| subsystem | funcs | bytes | files | matched | globals |")
    out("|---|---|---|---|---|---|")
    for members in multi[:a.top]:
        cluster_set = set(members)
        bases = sorted({b for b in base_groups
                        for m in by_base[b] if m in cluster_set})
        size = sum(int(x["end"], 16) - int(x["rom"], 16) for x in funcs
                   if int(x["rom"], 16) in cluster_set)
        pages = sorted({b >> 8 for b in bases if 0x02000000 <= b < 0x04000000})
        where = ", ".join(f"0x{p << 8:08X}" for p in pages) or "rom"
        got = sum(1 for m in members if f"{m:08X}" in matched)
        out(f"| `{where}` | {len(members)} | {size:,} | {len(carve(members))} | "
            f"{got} | {', '.join(f'0x{b:08X}' for b in bases[:2]) or '-'} |")

    out()
    out("## File candidates")
    out()
    out("Runs of 3+ functions, contiguous in the ROM - these are the things "
        "that")
    out("should become files.  Scattered runs are a shared struct, not a "
        "module.")
    out()
    out("| file | funcs | bytes | matched | globals | members |")
    out("|---|---|---|---|---|---|")
    files = []
    for members in multi:
        cluster_set = set(members)
        for run in carve(members):
            if len(run) < 3:
                continue
            bases = sorted({b for b in base_groups
                            for m in by_base[b] if m in cluster_set})
            size = sum(int(x["end"], 16) - int(x["rom"], 16) for x in funcs
                       if int(x["rom"], 16) in set(run))
            got = sum(1 for m in run if f"{m:08X}" in matched)
            files.append((run, size, got, bases))
    files.sort(key=lambda f: -f[1])
    for run, size, got, bases in files[:25]:
        name = f"module_{min(run) & 0xFFFFF0:06X}.c"
        head = ", ".join(f"0x{m:08X}" for m in run[:3])
        more = "" if len(run) <= 3 else f" +{len(run) - 3}"
        out(f"| `{name}` | {len(run)} | {size:,} | {got} | "
            f"{', '.join(f'0x{b:08X}' for b in bases[:2]) or '-'} | "
            f"{head}{more} |")

    out()
    out("## Identical code")
    out()
    out("Same function at two addresses - proof of a shared module, and a free "
        "match for whoever")
    out("reaches the second one.")
    out()
    for group in sorted(twins, key=lambda g: -len(g))[:20]:
        got = [f"0x{m:08X}" for m in sorted(group) if f"{m:08X}" in matched]
        out(f"- {', '.join(f'0x{m:08X}' for m in sorted(group))}"
            + (f"  (matched: {', '.join(got)})" if got else ""))

    out()
    out("## Mutual recursion")
    out()
    out("A cycle is hard to express across objects, so these belong together.")
    out()
    for comp in sorted(cycles, key=lambda c: -len(c))[:20]:
        out(f"- {', '.join(f'0x{m:08X}' for m in sorted(comp))}")

    out()
    out("## Shared globals, largest first")
    out()
    out("A global touched by several functions is a struct, and a struct is "
        "the reason")
    out("two functions end up in the same file.")
    out()
    out("| global | functions | sample |")
    out("|---|---|---|")
    for base, members in sorted(base_groups.items(), key=lambda kv: -len(kv[1]))[:25]:
        sample = ", ".join(f"0x{m:08X}" for m in sorted(members)[:4])
        out(f"| `0x{base:08X}` | {len(members)} | {sample} |")

    if a.moves:
        out("## Move plan")
        out()
        out("One file per function stays - agbcc compiles each source on its own "
            "and")
        out("match.py depends on that.  The folders are grouping: where the ROM "
            "evidence")
        out("says several functions were one source file, they live together.")
        out()
        moves = []
        for members in multi:
            member_set = set(members)
            bases = sorted({b for b in base_groups
                            for m in by_base[b] if m in member_set})
            # Name the folder for the subsystem, not for one contiguous run.
            # A run boundary is a guess about where the original file ended;
            # the RAM page is evidence about where the game's state lives, and
            # it does not move as more functions turn up.  Splitting one
            # subsystem across two folders because a run gap crossed 0x100
            # would be churn dressed up as structure.
            pages = [(len(by_base[b]), b >> 8) for b in bases
                     if 0x02000000 <= b < 0x04000000]
            if pages:
                folder = f"{max(pages)[1]:05x}"
            else:
                folder = f"{min(members) & 0xFFF000:06x}"
            for m in sorted(member_set):
                src = Path(root, "src", f"{m:08X}.c")
                if src.exists():
                    moves.append((f"src/{m:08X}.c",
                                  f"src/{folder}/{m:08X}.c", folder))
        if not moves:
            out("    (no source files fall in a candidate run)")
        for old, new, folder in moves:
            out(f"    {old}  ->  {new}")
        out(f"\n    {len(moves)} file(s) in {len({m[2] for m in moves})} "
            f"folder(s); the rest of src/ stays flat until evidence says "
            f"otherwise.")

    if a.out:
        path = a.out if os.path.isabs(a.out) else os.path.join(root, a.out)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8", newline="\n") as fh:
            fh.write("\n".join(lines) + "\n")
        print(f"\nwrote {path}")


if __name__ == "__main__":
    main()