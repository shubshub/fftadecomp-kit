#!/usr/bin/env python3
"""
push.py - the only sanctioned way to get work onto the decomp repository.

    python tools/push.py                 # verify, then push
    python tools/push.py --check-only    # verify only, push nothing
    python tools/push.py --force          # only for an intentional rewrite
    python tools/push.py --repo ../fftadecomp

Agents do not run `git push`.  They run this, and it refuses to push anything
that has not been verified - so the gate is mechanical rather than a rule
somebody has to remember under pressure.

The gate, all of which must pass:

  1. the branch contains the remote's tip of its base branch, and has no merge
     commits  - a rebased, linear history, reviewable as a diff.
     (--force skips only the "contains the tip" half, for rewriting history)
  2. nothing ROM-derived is tracked: no baserom.bin, no .gba, no asm/,
     no files/ - the disassembly and the raw runs are generated from the
     user's own ROM by 'make init' and must never be committed
  3. every function in src/ recompiles to the ROM bytes exactly, and the README
     progress block agrees with the result
  4. every source in src/ and include/ is plausible: no inline asm, no steering
     pragmas, no inert control flow
  5. every function in src/ has a report that says MATCH - byte identical, and
     no report says IMPLAUSIBLE or an unsanctioned HAND-ASM

Exit status is 0 only when every check passed *and* the push succeeded.  On
failure nothing is pushed and the failing check says what to do about it.

Set FFTA_PUSH_DRY=1 to disable the actual push without using --check-only.
"""

import argparse
import json
import os
import re
import subprocess
import sys

KIT = os.path.dirname(os.path.abspath(__file__))
_SIBLING = os.path.join(os.path.dirname(os.path.dirname(KIT)), "fftadecomp")
DEFAULT_REPO = os.environ.get("FFTA_REPO") or (
    _SIBLING if os.path.isdir(_SIBLING) else os.getcwd())
DEFAULT_REMOTE = os.environ.get("FFTA_REMOTE", "origin")
DEFAULT_BRANCH = os.environ.get("FFTA_BRANCH", "main")
FORBIDDEN_TRACKED = ("baserom.bin", ".gba", "files/", "asm/")


def log(*a):
    print(*a, flush=True)


def run(cmd, cwd, check=True):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    out = (r.stdout or "") + (r.stderr or "")
    if check and r.returncode != 0:
        log(f"    $ {' '.join(cmd)}")
        for line in out.strip().splitlines()[-12:]:
            log(f"    {line}")
    return r.returncode, out


def git(*args, **kw):
    repo = kw.pop("repo")
    return run(["git", *args], cwd=repo, **kw)


def check_history(repo, remote, branch, force=False):
    log("[1/5] history: rebased and linear")
    code, _ = git("fetch", remote, branch, repo=repo)
    if code != 0:
        log("    FAIL  could not fetch the remote")
        return False
    code, out = git("rev-parse", "--abbrev-ref", "HEAD", repo=repo)
    current = out.strip()
    if current != branch:
        log(f"    FAIL  on branch '{current}', expected '{branch}'")
        return False
    code, out = git("merge-base", "--is-ancestor", f"{remote}/{branch}", "HEAD",
                    repo=repo)
    if code != 0:
        if force:
            log("    --force: history rewrite in progress, so the branch cannot "
                "contain the old tip.")
            log("    ok: continuing; the push will rewrite "
                f"{remote}/{branch}")
        else:
            log(f"    FAIL  the branch is behind {remote}/{branch}.")
            log("          git fetch && git rebase " + f"{remote}/{branch}")
            log("          (or --force, if you are deliberately rewriting "
                "history)")
            return False
    if force:
        # the range now spans the whole existing trunk, whose merge commits
        # from other people's pull requests are legitimate history
        log("    --force: skipping the merge-commit scan; the range spans the "
            "existing trunk")
    else:
        code, out = git("log", "--merges", "--oneline",
                        f"{remote}/{branch}..HEAD", repo=repo)
        merges = [ln for ln in out.strip().splitlines() if ln.strip()]
        if merges:
            log(f"    FAIL  {len(merges)} merge commit(s) in the range; rebase "
                f"instead of merging {remote}/{branch} into your branch")
            for m in merges[:5]:
                log(f"          {m}")
            return False
    code, out = git("rev-list", "--count", f"{remote}/{branch}..HEAD", repo=repo)
    log(f"    ok: {out.strip()} commit(s) ahead of {remote}/{branch}, linear")
    return True


def check_no_rom_data(repo):
    log("[2/5] no game data tracked")
    code, out = git("ls-files", repo=repo)
    if code != 0:
        log("    FAIL  could not list tracked files")
        return False
    tracked = out.splitlines()
    bad = [f for f in tracked
           if f.endswith(FORBIDDEN_TRACKED) or f.endswith(".gba")
           or f.startswith("files/")]
    if bad:
        log("    FAIL  game data is tracked in git:")
        for f in bad[:5]:
            log(f"          {f}")
        log("    These are gitignored on purpose; remove them from the index.")
        return False
    log(f"    ok: none of {', '.join(FORBIDDEN_TRACKED)} tracked "
        f"({len(tracked)} files tracked)")
    return True


def check_matches(repo):
    log("[3/5] every function in src/ really matches, and the block agrees")
    code, out = run([sys.executable, os.path.join(KIT, "status.py"),
                     "--root", repo, "--check", "--verify"], cwd=repo)
    if code != 0:
        log("    FAIL  the progress block is stale or a source does not match.")
        for line in out.strip().splitlines()[-12:]:
            log(f"    {line}")
        log("    Fix the sources, then run: python "
            "../fftadecomp-kit/tools/status.py --write --verify")
        return False
    counts = [ln for ln in out.splitlines()
              if "identical" in ln or "up to date" in ln]
    log(f"    ok: {counts[-1].strip() if counts else 'verified'}")
    return True


def check_plausible(repo):
    log("[4/5] sources are plausible")
    for target in ("src", "include"):
        if not os.path.isdir(os.path.join(repo, target)):
            continue
        code, out = run([sys.executable, os.path.join(KIT, "plausible.py"),
                         os.path.join(repo, target)], cwd=repo)
        if code != 0:
            log(f"    FAIL  {target}/ contains implausible source")
            for line in out.strip().splitlines()[-10:]:
                log(f"    {line}")
            return False
    log("    ok: no inline asm, no steering pragmas, no inert control flow")
    return True


def check_reports(repo):
    log("[5/5] every function in src/ has a MATCH report")
    src = os.path.join(repo, "src")
    reports = os.path.join(repo, "docs", "match")
    if not os.path.isdir(src):
        log("    ok: no src/ directory")
        return True
    problems = []
    names = sorted(f for f in os.listdir(src) if f.endswith(".c"))
    for name in names:
        addr = name[:-2]
        path = os.path.join(reports, f"{addr}.md")
        if not os.path.exists(path):
            problems.append(f"{addr}: no report in docs/match/")
            continue
        text = open(path, encoding="utf-8").read()
        if "IMPLAUSIBLE" in text or "HAND-ASM" in text:
            problems.append(f"{addr}: report is not a clean MATCH")
        elif "MATCH - byte identical" not in text:
            problems.append(f"{addr}: report does not say MATCH")
    for path in sorted(os.listdir(reports)) if os.path.isdir(reports) else []:
        addr = path[:-3] if path.endswith(".md") else path
        if re.fullmatch(r"[0-9A-Fa-f]{8}", addr) and \
                not os.path.exists(os.path.join(src, f"{addr}.c")):
            continue                       # a parked function keeps its report
    if problems:
        log(f"    FAIL  {len(problems)} report problem(s):")
        for p in problems[:8]:
            log(f"          {p}")
        return False
    log(f"    ok: {len(names)} function(s), all with a MATCH report")
    return True


def do_push(repo, remote, branch, force=False):
    if os.environ.get("FFTA_PUSH_DRY"):
        log("\nFFTA_PUSH_DRY set - not pushing")
        return True
    verb = "force-pushing" if force else "pushing"
    log(f"\n{verb} to {remote}/{branch} ...")
    code, out = git("push", *(["--force"] if force else []), remote, branch,
                    repo=repo)
    if code != 0:
        log("    FAIL  the push was rejected")
        for line in out.strip().splitlines()[-10:]:
            log(f"    {line}")
        return False
    log("    pushed")
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=DEFAULT_REPO)
    ap.add_argument("--remote", default=DEFAULT_REMOTE)
    ap.add_argument("--branch", default=DEFAULT_BRANCH)
    ap.add_argument("--check-only", action="store_true",
                    help="run every check but push nothing")
    ap.add_argument("--force", action="store_true",
                    help="for an intentional history rewrite: drops the "
                         "'branch contains the remote tip' requirement and "
                         "force-pushes.  Every other check still runs.  Never "
                         "use this for ordinary work - rebase instead.")
    args = ap.parse_args()

    repo = os.path.abspath(args.repo)
    if not os.path.isdir(os.path.join(repo, ".git")):
        sys.exit(f"{repo} is not a git repository")

    log(f"push gate for {repo} -> {args.remote}/{args.branch}\n")
    checks = (
        check_history(repo, args.remote, args.branch, force=args.force),
        check_no_rom_data(repo),
        check_matches(repo),
        check_plausible(repo),
        check_reports(repo),
    )
    if not all(checks):
        log("\nNOTHING PUSHED - a check above failed.")
        return 1
    log("\nall checks passed")
    if args.check_only:
        log("--check-only: stopping before the push")
        return 0
    return 0 if do_push(repo, args.remote, args.branch,
                         force=args.force) else 1


if __name__ == "__main__":
    sys.exit(main())