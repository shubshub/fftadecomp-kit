#!/usr/bin/env python3
"""
probe.py - compile-shape experiments for one function.

    python tools/probe.py 0x0801CA10 --dir probes/0801CA10
    python tools/probe.py 0x0801CA10 --src src/0801CA10.c --dumps

When a function is *almost* right, the difference is usually not the algorithm
but a code-generation shape: whether a pointer lives in a register, whether an
offset folds into a MEM displacement, whether the frame survives at all.  Guessing
those one compile at a time is slow and tells you nothing until the end.

So: write the candidate shapes as separate .c files in a directory, point this
at them, and it reports each one's distance from the ROM - which slots agree,
where the first divergence is, and the shape-specific facts that explain the
rest (how many stack addresses are materialised into registers, whether the
symbol allocated a frame, how many bytes too long or short).

It never declares a match.  A shape that lands on the bytes still has to be
plausible C, and `plausible.py` is run over each variant so the report says so.
A byte-identical variant that trips the plausibility gate is shown as
IDENTICAL BUT IMPLAUSIBLE, not as progress.

    --dumps   keep agbcc's -da RTL dump beside each variant, which is where the
              real answer is (local_alloc and reload tell you why an address
              folded)
"""

import argparse
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    from match import Runner, disasm, lcs_align          # noqa: E402
except ImportError:                                      # pragma: no cover
    sys.exit("probe.py needs match.py beside it")

ROM_BASE = 0x08000000
DEFAULT_FLAGS = "-mthumb-interwork -O2"


def facts(insns):
    """shape facts that usually explain a near miss"""
    txt = [row[2] if isinstance(row, tuple) else
           f"{row.mnemonic} {row.op_str}".strip() for row in insns]
    sp_moves = sum(1 for t in txt if t.startswith("mov r") and t.endswith(", sp"))
    sp_adds = sum(1 for t in txt
                  if (t.startswith("add r") or t.startswith("adds r")) and ", sp" in t)
    return {
        "insns": len(txt),
        "sp_to_reg": sp_moves,          # addresses materialised into registers
        "sp_plus_off": sp_adds,         # sp base + immediate
        "frame": any(t.startswith("push {r") for t in txt)
        and any("sp" in t for t in txt if t.startswith("sub")),
    }


def compile_variant(runner, path, workdir, dumps=False):
    """cpp -> agbcc -> as -> objcopy; returns (bytes, rtl_dump_path|None)"""
    name = os.path.splitext(os.path.basename(path))[0]
    base = f"{workdir}/{name}"
    os.makedirs(workdir, exist_ok=True)
    dump = f"{base}.rtl" if dumps else os.devnull

    steps = [
        f"cpp -nostdinc -undef -I include {path} -o {base}.i",
        f"$AGBCC -mthumb-interwork -O2 -da {base}.i -o {base}.s",
        f"arm-none-eabi-as -mthumb-interwork {base}.s -o {base}.o",
        f"arm-none-eabi-objcopy -O binary --only-section=.text {base}.o {base}.bin",
    ]
    for step in steps:
        cmd = step.replace("$AGBCC",
                           os.environ.get("AGBCC", "$HOME/agbcc/gcc/agbcc"))
        runner.sh(cmd)
    if dumps:
        # agbcc writes the dump next to its output; normalise the name
        for cand in (f"{base}.s.rtl", f"{base}.rtl", f"{base}.da"):
            if os.path.exists(cand):
                os.replace(cand, dump)
                break
    return open(f"{base}.bin", "rb").read(), (dump if dumps else None)


def plausibility(path):
    here = os.path.dirname(os.path.abspath(__file__))
    r = subprocess.run([sys.executable, os.path.join(here, "plausible.py"),
                        "--quiet", path], capture_output=True, text=True)
    return r.returncode == 0, (r.stdout + r.stderr).strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("addr")
    ap.add_argument("--dir", help="directory of candidate .c shapes")
    ap.add_argument("--src", help="a single .c to try")
    ap.add_argument("--dumps", action="store_true",
                    help="keep agbcc's -da RTL dump beside each variant")
    ap.add_argument("--root", default=os.environ.get("FFTA_ROOT", "."))
    ap.add_argument("--top", type=int, default=3, help="how many to diff in full")
    args = ap.parse_args()

    addr = int(args.addr, 16)
    root = os.path.abspath(args.root)
    os.chdir(root)
    rom = open("baserom.bin", "rb").read()

    # the ROM extent: from the analysis, or to the end of the mapped function
    span = 0
    try:
        import json
        for f in json.load(open("config/functions.json", encoding="utf-8")):
            if int(f["rom"], 16) == addr:
                span = int(f["end"], 16) - addr
                break
    except (OSError, ValueError):
        pass
    if not span:
        span = 64
    want = rom[addr - ROM_BASE: addr - ROM_BASE + span]

    variants = []
    if args.src:
        variants.append(args.src)
    if args.dir:
        variants += [os.path.join(args.dir, f) for f in sorted(os.listdir(args.dir))
                     if f.endswith(".c")]
    if not variants:
        sys.exit("give --src or --dir with candidate shapes")

    runner = Runner(os.environ.get("AGBCC", "$HOME/agbcc/gcc/agbcc"),
                    os.environ.get("FFTA_WSL_DISTRO", "Ubuntu"),
                    os.environ.get("FFTA_WSL_PATH", "$HOME/armtc/root/usr/bin"))
    workdir = "/tmp/ffta_probe"

    print(f"probing {addr:08X} against {span} ROM bytes, "
          f"{len(variants)} shape(s)\n")
    print(f"{'shape':<28}{'bytes':>6}{'same':>6}{'ins':>5}{'sp2reg':>8}{'sp+off':>8}"
          f"{'frame':>7}  verdict")

    scored = []
    for path in variants:
        try:
            data, _ = compile_variant(runner, path, workdir, args.dumps)
        except Exception as exc:                          # noqa: BLE001
            detail = str(exc).strip().splitlines()
            print(f"{os.path.basename(path):<28}   compile failed: "
                  f"{detail[0] if detail else exc}")
            continue
        insns = disasm(data[:span], addr, True)
        f = facts(insns)
        rows = lcs_align([row[2] for row in insns],
                         [row[2] for row in disasm(want, addr, True)])
        same = sum(1 for k, _, _ in rows if k == "same")
        ok, detail = plausibility(path)
        verdict = ("IDENTICAL" if data == want else
                   f"{same}/{len(rows)} slots")
        if data == want and not ok:
            verdict = "IDENTICAL BUT IMPLAUSIBLE"
        elif not ok:
            verdict += "  (implausible)"
        print(f"{os.path.basename(path):<28}{len(data):>6}{same:>6}{f['insns']:>5}"
              f"{f['sp_to_reg']:>8}{f['sp_plus_off']:>8}{str(f['frame']):>7}  "
              f"{verdict}")
        scored.append((same, data, want, path, f, ok))

    if not scored:
        return 1
    scored.sort(key=lambda t: -t[0])
    best = scored[0]
    print(f"\nbest: {os.path.basename(best[3])}  {best[0]} slots agree, "
          f"{len(best[1])} bytes vs {len(best[2])}")
    if args.dumps:
        print(f"RTL dump for the winner: /tmp/ffta_probe/"
              f"{os.path.splitext(os.path.basename(best[3]))[0]}.rtl")
        print("  look for local_alloc (which pseudos exist) and reload "
              "(whether a plus folded into a MEM displacement)")
    if len(best[1]) != len(best[2]):
        print(f"  length differs by {len(best[1]) - len(best[2]):+d} bytes "
              f"({len(best[1])} vs {len(best[2])})")
    print()
    gi = [(f"{row[0]:08X}", row[2]) for row in disasm(best[1][:span], addr, True)]
    wi = [(f"{row[0]:08X}", row[2]) for row in disasm(best[2], addr, True)]
    for a, b in zip(gi, wi):
        mark = "   " if a[1] == b[1] else " <-"
        print(f"  {a[0]}  {a[1]:<26}{b[1]:<26}{mark}")
    if len(gi) != len(wi):
        print(f"  ({len(gi)} compiled instructions vs {len(wi)} in the ROM)")
    if not best[4]["frame"] and best[4]["sp_to_reg"] == 0:
        print("\n  note: no frame and no stack address in a register - the ROM "
              "keeps both")
    return 0 if best[1] == best[2] and best[5] else 1


if __name__ == "__main__":
    sys.exit(main())