"""Regenerate the progress block against what would actually be committed.

status.py reads the working tree, which is exactly wrong while sub-agents are
working in it: an agent landing or unlanding a src file changes the count
between --write and --check, and the commit ends up with a stale block.

This builds HEAD plus the staged files in a scratch directory - no in-flight
files - runs status.py --write --verify there, and copies the block back.  The
result is deterministic and matches what push.py will verify.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
from rompath import rom_path
import tempfile

KIT = os.path.dirname(os.path.abspath(__file__))


def sh(args, **kw):
    return subprocess.run(args, capture_output=True, text=True, **kw)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=".")
    ap.add_argument("--keep", action="store_true",
                    help="leave the scratch tree in place for inspection")
    a = ap.parse_args()
    repo = os.path.abspath(a.repo)

    head = sh(["git", "-C", repo, "rev-parse", "HEAD"])
    if head.returncode != 0:
        sys.exit("not a git repository")
    head = head.stdout.strip()

    staged = sh(["git", "-C", repo, "diff", "--cached", "--name-only"])
    # config/ and symbols/ matter as much as the sources: a match can be
    # rejected purely because its callee is missing from the index, so the
    # scratch tree needs the staged index too, not just the C
    files = [f for f in staged.stdout.splitlines()
             if f.startswith(("src/", "include/", "docs/match/", "config/",
                              "symbols/"))]

    tmp = tempfile.mkdtemp(prefix="ffta_block_")
    arc = subprocess.run(["git", "-C", repo, "archive", head],
                         capture_output=True)
    if arc.returncode != 0 or subprocess.run(
            ["tar", "-x", "-C", tmp], input=arc.stdout,
            capture_output=True).returncode != 0:
        sys.exit("could not materialise HEAD")

    for f in files:
        blob = sh(["git", "-C", repo, "show", f":{f}"])
        if blob.returncode != 0:
            continue
        dst = os.path.join(tmp, f.replace("/", os.sep))
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(dst, "wb") as fh:
            fh.write(blob.stdout.encode("latin1", "replace")
                     if isinstance(blob.stdout, str) else b"")
        if blob.stderr:
            pass

    rom = rom_path(repo)
    if rom and os.path.exists(rom):
        shutil.copy2(rom, os.path.join(tmp, "baserom.bin"))

    env = dict(os.environ)
    env["PATH"] = env.get("PATH", "")
    # the scratch tree has no .git, so status.py cannot derive the badge base
    # from the remote and falls back to static badges - which then reads as a
    # stale block the moment the gate checks the commit
    remote = sh(["git", "-C", repo, "remote", "get-url", "origin"]).stdout.strip()
    import re as _re
    m = _re.search(r"github\.com[:/]([^/]+)/([^/\s]+?)(?:\.git)?$", remote)
    cmd = [sys.executable, os.path.join(KIT, "status.py"),
           "--root", tmp, "--write", "--verify"]
    if m:
        cmd += ["--badge-base",
                f"https://raw.githubusercontent.com/{m.group(1)}/{m.group(2)}/badges"]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    out = (r.stdout + r.stderr).strip()
    print(f"status of the staged tree ({len(files)} staged source file(s)):")
    for ln in out.splitlines()[-6:]:
        print("   " + ln)

    for name in ("README.md", os.path.join("docs", "status.md")):
        src = os.path.join(tmp, name)
        if os.path.exists(src):
            shutil.copy2(src, os.path.join(repo, name))
            print(f"updated {name}")

    if not a.keep:
        shutil.rmtree(tmp, ignore_errors=True)
    else:
        print("scratch tree kept at", tmp)


if __name__ == "__main__":
    main()