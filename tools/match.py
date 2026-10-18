#!/usr/bin/env python3
"""
match.py - compile src/<addr>.c and diff it against the ROM bytes.

    python tools/match.py 0x08017514
    python tools/match.py --flags "-mthumb-interwork -O1" 0x080112D4
    python tools/match.py --cc clang --flags "--target=arm-none-eabi -mthumb -O2" 0x...

Toolchain: agbcc (gcc 2.9-arm-000512 for Thumb/elf) is the compiler that
built the ROM.  It is a cc1, so it emits assembly and the file has to be
assembled and stripped before the bytes can be compared:

    agbcc <flags> src.c -o out.s
    arm-none-eabi-as -mthumb-interwork out.s -o out.o
    arm-none-eabi-objcopy -O binary --only-section=.text out.o out.bin

On Windows with WSL the whole chain runs inside the distro and the bytes are
read back over.  The verdict is byte-exact or it is not; the report shows which
instruction the compiler decided differently.
"""

import argparse
import os
import platform
import shutil
import subprocess
import sys
import tempfile

try:
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB
except ImportError:
    sys.exit("match.py needs capstone:  python -m pip install capstone")

def repo_root(arg=None):
    """The decomp repo this tool operates on.

    Defaults to the current directory (or $FFTA_ROOT), so the tools can live
    in their own repository - see fftadecomp-kit.
    """
    return os.path.abspath(arg or os.environ.get("FFTA_ROOT") or os.getcwd())


ROOT = repo_root()
ROM_BASE = 0x08000000

DEFAULT_CC = "$HOME/agbcc/gcc/agbcc"
DEFAULT_CPP = "cpp"
DEFAULT_AS = "arm-none-eabi-as"
DEFAULT_OBJCOPY = "arm-none-eabi-objcopy"
DEFAULT_FLAGS = "-mthumb-interwork -O2"
DEFAULT_WSL_PATH = "$HOME/armtc/root/usr/bin"


class Runner:
    """Runs shell commands, transparently through WSL on Windows."""

    def __init__(self, cc, wsl_distro="Ubuntu", wsl_path=""):
        self.wsl = None
        self.prefix = f"export PATH={wsl_path}:$PATH; " if wsl_path else ""
        if platform.system() == "Windows" and not shutil.which(cc.split("/")[-1]):
            wsl = shutil.which("wsl")
            if wsl:
                self.wsl = [wsl, "-d", wsl_distro, "-e", "bash", "-lc"]

    def sh(self, cmd):
        if self.wsl:
            here = "/mnt/c/" + "/".join(ROOT[3:].split(os.sep))
            cmd = f"{self.prefix}cd {here} && {cmd}"
            r = subprocess.run(self.wsl + [cmd], capture_output=True, text=True)
        else:
            r = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError((r.stderr or r.stdout or "command failed").strip())
        return r.stdout

    def read_binary(self, path):
        if self.wsl:
            out = subprocess.run(self.wsl + [f"xxd -p {path}"],
                                 capture_output=True, text=True).stdout
            return bytes.fromhex("".join(out.split()))
        with open(path, "rb") as f:
            return f.read()


def lcs_align(a, b):
    """align two sequences, reporting which elements are shared"""
    n, m = len(a), len(b)
    dp = [[0] * (m + 1) for _ in range(n + 1)]
    for i in range(n - 1, -1, -1):
        for j in range(m - 1, -1, -1):
            dp[i][j] = dp[i + 1][j + 1] + 1 if a[i] == b[j] \
                else max(dp[i + 1][j], dp[i][j + 1])
    i = j = 0
    rows = []
    while i < n and j < m:
        if a[i] == b[j]:
            rows.append(("same", a[i], b[j]))
            i += 1
            j += 1
        elif dp[i + 1][j] >= dp[i][j + 1]:
            rows.append(("got", a[i], None))
            i += 1
        else:
            rows.append(("want", None, b[j]))
            j += 1
    rows += [("got", x, None) for x in a[i:]]
    rows += [("want", None, x) for x in b[j:]]
    return rows


def disasm(data, base, thumb):
    cs = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
    return [(i.address, i.size, f"{i.mnemonic} {i.op_str}".strip())
            for i in cs.disasm(data, base)]


def function_span(addr, symbols_file):
    """length of the ROM function at addr, from symbols/functions.txt"""
    with open(symbols_file, encoding="utf-8") as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            p = line.split()                    # addr end size instrs endby
            a = int(p[0], 16)
            if a == addr:
                return int(p[1], 16) - a
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("addr")
    ap.add_argument("--cc", default=DEFAULT_CC)
    ap.add_argument("--cpp", default=DEFAULT_CPP)
    ap.add_argument("--assembler", dest="assembler", default=DEFAULT_AS)
    ap.add_argument("--objcopy", default=DEFAULT_OBJCOPY)
    ap.add_argument("--flags", default=DEFAULT_FLAGS)
    ap.add_argument("--mode", default="thumb", choices=("thumb", "arm"))
    ap.add_argument("--wsl", default="Ubuntu")
    ap.add_argument("--wsl-path", default=os.environ.get("FFTA_WSL_PATH",
                                                         DEFAULT_WSL_PATH))
    ap.add_argument("--label", default="")
    ap.add_argument("--no-write", action="store_true")
    ap.add_argument("--root", default=os.environ.get("FFTA_ROOT"),
                    help="decomp repo (default: current directory)")
    args = ap.parse_args()
    global ROOT
    ROOT = repo_root(args.root)

    addr = int(args.addr, 16)
    src_rel = f"src/{addr:08X}.c"
    src_abs = os.path.join(ROOT, "src", f"{addr:08X}.c")
    if not os.path.exists(src_abs):
        sys.exit(f"no source at {src_abs}")

    rom = open(os.path.join(ROOT, "baserom.bin"), "rb").read()
    span = function_span(addr, os.path.join(ROOT, "symbols", "functions.txt"))
    span = span or 0x40
    want = rom[addr - ROM_BASE: addr - ROM_BASE + span]
    thumb = args.mode == "thumb"

    print(f"function  0x{addr:08X}   {span} bytes ({'Thumb' if thumb else 'ARM'})")
    print(f"source    {src_rel}")
    print(f"compiler  {args.cc} {args.flags}")

    # the compile runs in a shell (possibly inside WSL), so give it a POSIX path
    tmp = "/tmp/ffta_match_%s" % os.urandom(4).hex()
    runner = Runner(args.cc, args.wsl, args.wsl_path)
    try:
        runner.sh(f"mkdir -p {tmp}")
        # agbcc is a raw cc1: it does not preprocess, so expand includes,
        # macros and comments first
        runner.sh(f"{args.cpp} -nostdinc -undef -I include {src_rel} -o {tmp}/f.i")
        runner.sh(f"{args.cc} {args.flags} {tmp}/f.i -o {tmp}/f.s")
        if thumb:
            runner.sh(f"{args.assembler} -mthumb-interwork {tmp}/f.s -o {tmp}/f.o")
        else:
            runner.sh(f"{args.assembler} {tmp}/f.s -o {tmp}/f.o")
        runner.sh(f"{args.objcopy} -O binary --only-section=.text "
                  f"{tmp}/f.o {tmp}/f.bin")
        got = runner.read_binary(f"{tmp}/f.bin")
    except Exception as e:                       # noqa: BLE001
        sys.exit(f"compile failed:\n{e}")

    got_body = got[:span]
    exact = got_body == want
    byte_rows = lcs_align(got_body, want)

    print(f"\ntarget  {want.hex()}")
    print(f"got     {got_body.hex()}"
          + ("" if len(got) == span else f"   ({len(got)} bytes compiled)"))
    print(f"verdict {'MATCH - byte identical' if exact else 'differs'}\n")

    ga, wa = disasm(got, addr, thumb), disasm(want, addr, thumb)
    gbytes = [t for _, _, t in ga]
    wbytes = [t for _, _, t in wa]
    past_end = {i for i, (a, _, _) in enumerate(ga) if a >= addr + span}
    rows = lcs_align(gbytes, wbytes)

    width = 40
    lines, gi, wi = [], 0, 0
    for kind, _, _ in rows:
        g = gbytes[gi] if gi < len(gbytes) else ""
        w = wbytes[wi] if wi < len(wbytes) else ""
        if kind == "same":
            lines.append(f"{g:<{width}}{w}")
        elif kind == "got":
            over = "  (past the ROM function)" if gi in past_end else ""
            lines.append(f"{g:<{width}}{'':<{width}}  <- extra in compiled{over}")
        else:
            lines.append(f"{'':<{width}}{w:<{width}}  <- missing from compiled")
        gi += 1 if kind != "want" else 0
        wi += 1 if kind != "got" else 0

    print(f"{'compiled':<{width}}{'rom':<{width}}")
    print(f"{'-' * width}{'-' * 40}")
    for line in lines:
        print(line)

    same_bytes = sum(1 for k, _, _ in byte_rows if k == "same")
    same_instr = sum(1 for k, _, _ in rows if k == "same")
    print(f"\n{same_instr}/{len(wbytes)} instructions identical "
          f"({same_bytes}/{len(want)} bytes)")

    if not args.no_write:
        label = f".{args.label}" if args.label else ""
        out = os.path.join(ROOT, "docs", "match", f"{addr:08X}{label}.md")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        with open(out, "w", encoding="utf-8", newline="\n") as f:
            f.write(f"# match report - 0x{addr:08X}"
                    f"{' (' + args.label + ')' if args.label else ''}\n\n")
            f.write(f"* source: `{src_rel}`\n")
            f.write(f"* compiler: `{args.cc} {args.flags}`\n")
            f.write(f"* ROM bytes: `{want.hex()}` ({span} bytes)\n")
            f.write(f"* compiled : `{got_body.hex()}`\n\n")
            f.write(f"**{'MATCH - byte identical' if exact else 'NOT matching'}**"
                    f" - {same_bytes}/{len(want)} bytes\n\n```\n")
            f.write(f"{'compiled':<{width}}{'rom':<{width}}\n")
            for line in lines:
                f.write(line + "\n")
            f.write("```\n")
        print(f"\nwrote {os.path.relpath(out, ROOT)}")
    return 0 if exact else 1


if __name__ == "__main__":
    sys.exit(main())