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
import shlex
import shutil
import struct
import subprocess
import sys
from contextlib import contextmanager
from match_evidence import SCHEMA, source_fingerprint, source_paths, verify_dependencies

try:
    from capstone import (Cs, CS_ARCH_ARM, CS_MODE_ARM, CS_MODE_THUMB,
                          CS_GRP_CALL, CS_GRP_JUMP, CS_GRP_INT)
    from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_OP_MEM,
                                    ARM_OP_REG, ARM_REG_LR, ARM_REG_PC, ARM_REG_SP)
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
            r = subprocess.run(cmd, shell=True, capture_output=True, text=True,
                               cwd=ROOT)
        if r.returncode != 0:
            raise RuntimeError((r.stderr or r.stdout or "command failed").strip())
        return r.stdout

    def read_binary(self, path):
        if self.wsl:
            out = self.sh(f"xxd -p {shlex.quote(path)}")
            return bytes.fromhex("".join(out.split()))
        with open(path, "rb") as f:
            return f.read()

    @contextmanager
    def workspace(self):
        path = self.sh('mkdir -p build && mktemp -d "$PWD/build/ffta_match_XXXXXXXX"').strip()
        if not path:
            raise RuntimeError("could not create compilation workspace")
        try:
            yield path
        finally:
            outputs = " ".join(shlex.quote(f"{path}/f.{suffix}")
                               for suffix in ("i", "s", "o", "bin"))
            self.sh(f"rm -f -- {outputs} && rmdir -- {shlex.quote(path)}")


def function_bytes(object_data, text_data, name, address, thumb):
    """Read the complete named function, including its pool, from ARM ELF32."""
    if object_data[:7] != b"\x7fELF\x01\x01\x01":
        raise ValueError("expected a little-endian ELF32 object")
    header = struct.unpack_from("<HHIIIIIHHHHHH", object_data, 16)
    object_type, machine = header[:2]
    section_offset, section_size, section_count, names_index = (
        header[5], header[10], header[11], header[12])
    if object_type != 1 or machine != 40 or section_size != 40:
        raise ValueError("expected an ARM relocatable ELF32 object")
    sections = [struct.unpack_from("<IIIIIIIIII", object_data,
                                  section_offset + index * section_size)
                for index in range(section_count)]

    def section_data(section):
        start, size = section[4:6]
        result = object_data[start:start + size]
        if len(result) != size:
            raise ValueError("truncated ELF section")
        return result

    def string_at(strings, offset):
        return strings[offset:strings.index(b"\0", offset)].decode("ascii")

    section_names = section_data(sections[names_index])
    text_sections = [index for index, section in enumerate(sections)
                     if string_at(section_names, section[0]) == ".text"]
    if len(text_sections) != 1:
        raise ValueError("expected exactly one .text section")
    text_index = text_sections[0]
    if section_data(sections[text_index]) != text_data:
        raise ValueError("objcopy output does not equal ELF .text")
    if any(section[1] in (4, 9) and section[5] for section in sections):
        raise ValueError("unresolved relocations: link the object before comparing ROM bytes")

    matches = []
    for section in sections:
        if section[1] != 2:
            continue
        if section[9] != 16 or section[5] % 16:
            raise ValueError("invalid ELF symbol table")
        strings = section_data(sections[section[6]])
        symbols = section_data(section)
        for offset in range(0, len(symbols), 16):
            symbol_name, value, size, info, visibility, section_index = (
                struct.unpack_from("<IIIBBH", symbols, offset))
            if string_at(strings, symbol_name) != name:
                continue
            if info & 15 != 2 or section_index != text_index or not size:
                raise ValueError(f"{name} is not a sized .text function")
            start = value & ~1
            if bool(value & 1) != thumb:
                raise ValueError(f"{name} ELF instruction mode does not match requested mode")
            if start % 4 != address % 4 or address % (2 if thumb else 4):
                raise ValueError(f"{name} ELF and ROM alignment differ")
            if start + size > len(text_data):
                raise ValueError(f"{name} extends beyond .text")
            matches.append(text_data[start:start + size])
    if len(matches) != 1:
        raise ValueError(f"expected exactly one ELF function named {name}")
    return matches[0]


def verify_leaf(data, address, thumb):
    """Certify a closed straight-line body and its PC-relative literal reads."""
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
    decoder.detail = True
    return_registers = {ARM_REG_LR}
    stack = []
    literals = []
    for instruction in decoder.disasm(data, address):
        operands = instruction.operands
        registers = tuple(operand.reg for operand in operands if operand.type == ARM_OP_REG)
        unconditional = instruction.cc in (ARM_CC_AL, ARM_CC_INVALID)
        if instruction.mnemonic in ("push", "pop"):
            if not unconditional or ARM_REG_SP in registers:
                raise ValueError("unsupported conditional or irregular stack operation")
            if instruction.mnemonic == "push":
                stack[:0] = [register in return_registers for register in registers]
                continue
            if len(registers) > len(stack):
                raise ValueError("pop reads outside the saved stack frame")
            for register, saved_return in zip(registers, stack):
                return_registers.discard(register)
                if saved_return:
                    return_registers.add(register)
            del stack[:len(registers)]
            if ARM_REG_PC not in registers:
                continue
        returning = unconditional and (
            (instruction.mnemonic == "bx" and len(registers) == 1 and
             registers[0] in return_registers) or
            (instruction.mnemonic == "pop" and ARM_REG_PC in return_registers) or
            (instruction.mnemonic == "mov" and registers == (ARM_REG_PC, ARM_REG_LR)
             and ARM_REG_LR in return_registers))
        if returning:
            if stack:
                raise ValueError("return does not balance the saved stack frame")
            code_end = instruction.address + instruction.size
            if any(literal < code_end or literal + 4 > address + len(data)
                   for literal in literals):
                raise ValueError("literal read is outside the function's trailing pool")
            return code_end - address
        if any(group in instruction.groups for group in (CS_GRP_CALL, CS_GRP_JUMP, CS_GRP_INT)):
            raise ValueError("non-leaf control flow requires linked CFG verification")
        written = instruction.regs_access()[1]
        if ARM_REG_PC in written:
            raise ValueError("unresolved program-counter write")
        if ARM_REG_SP in written:
            raise ValueError("unsupported stack-pointer adjustment")
        if ARM_REG_SP in registers:
            raise ValueError("unsupported stack-address materialization")
        for operand in operands:
            if operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_PC:
                if instruction.mnemonic != "ldr" or operand.mem.index:
                    raise ValueError("unsupported PC-relative memory access")
                program_counter = ((instruction.address + 4) & ~3
                                   if thumb else instruction.address + 8)
                literals.append(program_counter + operand.mem.disp)
            if operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_SP:
                if not instruction.mnemonic.startswith("ldr"):
                    raise ValueError("unsupported stack-frame write")
        return_registers.difference_update(written)
    raise ValueError("function has no verified return")


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
    fingerprint = source_fingerprint(ROOT, addr)

    rom = open(os.path.join(ROOT, "baserom.bin"), "rb").read()
    span = function_span(addr, os.path.join(ROOT, "symbols", "functions.txt"))
    if span is None or span <= 0:
        sys.exit(f"no valid indexed span for 0x{addr:08X}")
    if not ROM_BASE <= addr < ROM_BASE + len(rom):
        sys.exit("function address is outside the ROM")
    thumb = args.mode == "thumb"

    print(f"function  0x{addr:08X}   {span} bytes ({'Thumb' if thumb else 'ARM'})")
    print(f"source    {src_rel}")
    print(f"compiler  {args.cc} {args.flags}")

    # the compile runs in a shell (possibly inside WSL), so give it a POSIX path
    runner = Runner(args.cc, args.wsl, args.wsl_path)
    try:
        with runner.workspace() as workspace:
            tmp = shlex.quote(workspace)
            environment = f"export TMPDIR={tmp}; "
            runner.sh(f"{environment}{args.cpp} -nostdinc -undef -I include {src_rel} -o {tmp}/f.i")
            verify_dependencies(runner.read_binary(f"{workspace}/f.i").decode("utf-8"), ROOT, addr)
            runner.sh(f"{environment}{args.cc} {args.flags} {tmp}/f.i -o {tmp}/f.s")
            assembler_flags = "-mthumb-interwork" if thumb else ""
            runner.sh(f"{environment}{args.assembler} {assembler_flags} {tmp}/f.s -o {tmp}/f.o")
            runner.sh(f"{args.objcopy} -O binary --only-section=.text "
                      f"{tmp}/f.o {tmp}/f.bin")
            got = function_bytes(runner.read_binary(f"{workspace}/f.o"),
                                 runner.read_binary(f"{workspace}/f.bin"),
                                 f"func_{addr:08X}", addr, thumb)
            code_size = verify_leaf(got, addr, thumb)
    except Exception as e:                       # noqa: BLE001
        sys.exit(f"compile failed:\n{e}")

    if len(got) < span:
        sys.exit(f"compiled symbol is shorter than the indexed span: {len(got)} < {span}")
    span = len(got)
    print(f"extent    {span} bytes (complete ELF symbol; closed leaf; no relocations)")
    want = rom[addr - ROM_BASE: addr - ROM_BASE + span]
    got_body = got
    identical = got_body == want

    # a byte-identical compile is only a match if the source is something a
    # developer could plausibly have written
    here = os.path.dirname(os.path.abspath(__file__))
    plaus_path = os.path.join(here, "plausible.py")
    findings = ["plausibility checker is missing"]
    if os.path.exists(plaus_path):
        lint_targets = [str(path) for path in source_paths(ROOT, addr)]
        r = subprocess.run([sys.executable, plaus_path, "--quiet"] + lint_targets,
                           capture_output=True, text=True)
        findings = [ln for ln in r.stdout.splitlines() if ln.strip()]
        if r.returncode and not findings:
            findings = [ln for ln in r.stderr.splitlines() if ln.strip()]
            if not findings:
                findings = [f"plausibility checker failed with exit {r.returncode}"]

    plausible = not findings
    if source_fingerprint(ROOT, addr) != fingerprint:
        sys.exit("source or headers changed during verification; re-run match.py")
    exact = identical and plausible
    byte_rows = lcs_align(got_body, want)

    print(f"\ntarget  {want.hex()}")
    print(f"got     {got_body.hex()}"
          + ("" if len(got) == span else f"   ({len(got)} bytes compiled)"))
    print(f"bytes   {'identical' if identical else 'DIFFER'}")
    print(f"source  {'plausible' if plausible else 'IMPLAUSIBLE'}")
    print(f"verdict {'MATCH - byte identical' if exact else
                 ('IMPLAUSIBLE - bytes match but the source is not code a '
                  'developer would have written' if identical else
                  'NOT MATCHING - bytes differ')}\n")
    if findings:
        print("plausibility findings:")
        for line in findings:
            print(f"  {line}")

    ga = disasm(got[:code_size], addr, thumb)
    wa = disasm(want[:code_size], addr, thumb)
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

    print(f"{'compiled':<{width}}rom")
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
            f.write(f"* verification: `{SCHEMA}`\n")
            f.write(f"* source SHA-256: `{fingerprint}`\n")
            f.write(f"* compiler: `{args.cc} {args.flags}`\n")
            f.write(f"* verified extent: complete ELF function symbol, including literal pools\n")
            f.write(f"* relocations: none\n")
            f.write(f"* ROM bytes: `{want.hex()}` ({span} bytes)\n")
            f.write(f"* compiled : `{got_body.hex()}`\n")
            f.write(f"* source plausibility: "
                    f"{'plausible' if plausible else 'IMPLAUSIBLE'}\n\n")
            verdict = ("MATCH - byte identical" if exact else
                       "IMPLAUSIBLE - bytes match but the source is not code a "
                       "developer would have written" if identical else
                       "NOT MATCHING - bytes differ")
            f.write(f"**{verdict}** - {same_bytes}/{len(want)} bytes\n")
            if findings:
                f.write("\nplausibility findings:\n\n")
                for line in findings:
                    f.write(f"- {line.strip()}\n")
            f.write("\n```\n")
            f.write(f"{'compiled':<{width}}rom\n")
            for line in lines:
                f.write(line.rstrip() + "\n")
            f.write("```\n")
        print(f"\nwrote {os.path.relpath(out, ROOT)}")
    return 0 if exact else 1


if __name__ == "__main__":
    sys.exit(main())
