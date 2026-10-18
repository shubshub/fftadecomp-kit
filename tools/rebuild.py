#!/usr/bin/env python3
"""
rebuild.py - prove the split is lossless, and check the assembled ROM.

  python tools/rebuild.py            concatenate files/*.bin in manifest order
                                     and compare SHA1 against baserom.bin
  python tools/rebuild.py --armips   assemble asm/*.s with armips first, then
                                     compare that output instead

Byte-exactness matters more than speed here: if the concatenation does not
reproduce the base ROM, the split is wrong and nothing downstream is safe.
"""

import hashlib
import json
import os
import subprocess
import sys

ROM_BASE = 0x08000000


def repo_root(arg=None):
    """The decomp repo this tool operates on.

    Defaults to the current directory (or $FFTA_ROOT), so the tools can live
    in their own repository - see fftadecomp-kit.
    """
    return os.path.abspath(arg or os.environ.get("FFTA_ROOT") or os.getcwd())


def sha1(data):
    return hashlib.sha1(data).hexdigest().upper()


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    here = repo_root(args[0] if args else None)
    rom_path = os.path.join(here, "baserom.bin")
    base = open(rom_path, "rb").read()
    manifest = json.load(open(os.path.join(here, "asm", "manifest.json")))

    print(f"base ROM : {os.path.basename(rom_path)}")
    print(f"  size   : {len(base):,}")
    print(f"  sha1   : {sha1(base)}")

    if "--armips" in sys.argv:
        out = os.path.join(here, "build", "ffta.gba")
        os.makedirs(os.path.dirname(out), exist_ok=True)
        script = os.path.join(here, "asm", "ffta.s")
        cmd = ["armips", script]
        print(f"\nassembling: {' '.join(cmd)}")
        try:
            subprocess.run(cmd, check=True, cwd=here)
        except FileNotFoundError:
            sys.exit("armips not found: install it first (see tools/bootstrap.sh)")
        built = open(out, "rb").read()
    else:
        built = bytearray()
        for part in manifest["parts"]:
            data = open(os.path.join(here, part["path"]), "rb").read()
            built += data
        built = bytes(built)

    print(f"\nrebuilt  : {len(built):,} bytes from {len(manifest['parts'])} parts")
    print(f"  sha1   : {sha1(built)}")

    if built == base:
        print("\nOK - the split reproduces the base ROM byte for byte")
        return 0

    print("\nMISMATCH")
    if len(built) != len(base):
        print(f"  size differs by {len(built) - len(base):+,}")
    n = min(len(built), len(base))
    first = next((i for i in range(n) if built[i] != base[i]), n)
    print(f"  first difference at 0x{ROM_BASE + first:08X} "
          f"(file offset 0x{first:X})")
    for i in range(max(0, first - 8), min(n, first + 8)):
        mark = "<<" if i == first else "  "
        print(f"    {ROM_BASE+i:08X}  base {base[i]:02X}  built {built[i]:02X} {mark}")
    return 1


if __name__ == "__main__":
    sys.exit(main())