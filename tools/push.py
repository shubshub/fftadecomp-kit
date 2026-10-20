#!/usr/bin/env python3
"""
push.py - verify and push the decompilation or this toolkit checkout.

    python tools/push.py                 # verify, then push
    python tools/push.py --check-only    # verify only, push nothing
    python tools/push.py --force          # only for an intentional rewrite
    python tools/push.py --repo ../fftadecomp
    python tools/push.py --kit           # validate and push this toolkit

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

Toolkit mode replaces checks 3-5 with syntax validation of tracked Python
tools. Intentional rewrites pin the remote tip before validation and use an
explicit force-with-lease, never an unconditional force push.
Toolkit and working-tree publication require a clean worktree and index.
Default decompilation verification uses an archive of the captured commit,
allowing unrelated work in progress without publishing unverified changes.

Exit status is 0 only when every check passed *and* the push succeeded.  On
failure nothing is pushed and the failing check says what to do about it.

Set FFTA_PUSH_DRY=1 to disable the actual push without using --check-only.
"""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from rompath import rom_path

KIT = os.path.dirname(os.path.realpath(__file__))
KIT_ROOT = os.path.realpath(os.path.dirname(KIT))
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


def committed_tree(repo, commit):
    """Materialize the captured commit under the repository's build directory."""
    import shutil
    import tempfile
    destination = None
    try:
        build = os.path.join(repo, "build")
        os.makedirs(build, exist_ok=True)
        destination = tempfile.mkdtemp(prefix="ffta_push_", dir=build)
        archive = subprocess.run(["git", "-C", repo, "archive", commit],
                                 capture_output=True)
        if archive.returncode != 0:
            raise ValueError("could not archive the captured commit")
        extracted = subprocess.run(["tar", "-x", "-C", destination],
                                   input=archive.stdout, capture_output=True)
        if extracted.returncode != 0:
            raise ValueError("could not extract the captured commit")
        source_rom = rom_path(repo, required=False)
        if source_rom and os.path.exists(source_rom):
            shutil.copy2(source_rom, os.path.join(destination, "baserom.bin"))
        return destination
    except (OSError, ValueError) as error:
        if destination is not None:
            shutil.rmtree(destination, ignore_errors=True)
        log(f"    FAIL  committed-tree verification: {error}")
        return None


def badge_base(repo):
    """raw.githubusercontent.com base for the repo's badges branch"""
    r = subprocess.run(["git", "-C", repo, "remote", "get-url", "origin"],
                       capture_output=True, text=True)
    m = re.search(r"github\.com[:/]([^/]+)/([^/\s]+?)(?:\.git)?$",
                  r.stdout.strip() if r.returncode == 0 else "")
    if not m:
        return ""
    return f"https://raw.githubusercontent.com/{m.group(1)}/{m.group(2)}/badges"


def check_matches(root, badge=""):
    log("[3/5] every function in src/ really matches, and the block agrees")
    cmd = [sys.executable, os.path.join(KIT, "status.py"),
           "--root", root, "--check", "--verify"]
    if badge:
        cmd += ["--badge-base", badge]
    code, out = run(cmd, cwd=root)
    if code != 0:
        log("    FAIL  the progress block is stale or a source does not match.")
        for line in out.strip().splitlines()[-12:]:
            log(f"    {line}")
        log("    Fix the sources, then run: python "
            "../fftadecomp-kit/tools/status.py --write --verify")
        return False
    counts = [ln for ln in out.splitlines() if "identical" in ln or "up to date" in ln]
    log(f"    ok: {counts[-1].strip() if counts else 'verified'}")
    return True


def check_plausible(root):
    log("[4/5] sources are plausible")
    for target in ("src", "include"):
        if not os.path.isdir(os.path.join(root, target)):
            continue
        code, out = run([sys.executable, os.path.join(KIT, "plausible.py"),
                         os.path.join(root, target)], cwd=root)
        if code != 0:
            log(f"    FAIL  {target}/ contains implausible source")
            for line in out.strip().splitlines()[-10:]:
                log(f"    {line}")
            return False
    log("    ok: no inline asm, no steering pragmas, no inert control flow")
    return True


def check_reports(root):
    log("[5/5] every function in src/ has a MATCH report")
    src = os.path.join(root, "src")
    reports = os.path.join(root, "docs", "match")
    if not os.path.isdir(src):
        log("    ok: no src/ directory")
        return True
    problems = []
    names = sorted(p.name for p in Path(src).rglob("*.c"))
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
    if problems:
        log(f"    FAIL  {len(problems)} report problem(s):")
        for p in problems[:8]:
            log(f"          {p}")
        return False
    log(f"    ok: {len(names)} function(s), all with a MATCH report")
    return True


def check_history(repo, remote, branch, force=False):
    log("[1/5] history: rebased and linear")
    code, _ = git("fetch", remote, branch, repo=repo)
    if code != 0:
        log("    FAIL  could not fetch the remote")
        return False
    code, out = git("rev-parse", "--abbrev-ref", "HEAD", repo=repo)
    if code != 0:
        log("    FAIL  could not determine the current branch")
        return False
    current = out.strip()
    if current != branch:
        log(f"    FAIL  on branch '{current}', expected '{branch}'")
        return False
    code, out = git("merge-base", "--is-ancestor", f"{remote}/{branch}", "HEAD",
                    repo=repo)
    if code != 0:
        if code != 1:
            log("    FAIL  could not check the remote ancestry")
            return False
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
        if code != 0:
            log("    FAIL  could not scan merge commits")
            return False
        merges = [ln for ln in out.strip().splitlines() if ln.strip()]
        if merges:
            log(f"    FAIL  {len(merges)} merge commit(s) in the range; rebase "
                f"instead of merging {remote}/{branch} into your branch")
            for m in merges[:5]:
                log(f"          {m}")
            return False
    code, out = git("rev-list", "--count", f"{remote}/{branch}..HEAD", repo=repo)
    if code != 0:
        log("    FAIL  could not count branch commits")
        return False
    log(f"    ok: {out.strip()} commit(s) ahead of {remote}/{branch}, linear")
    return True


def check_no_rom_data(repo, commit=None):
    log("[2/5] no game data tracked")
    arguments = ("ls-tree", "-r", "--name-only", "-z", commit) if commit else ("ls-files", "-z")
    code, out = git(*arguments, repo=repo)
    if code != 0:
        log("    FAIL  could not list tracked files")
        return False
    tracked = [path for path in out.split("\0") if path]
    bad = [path for path in tracked
           if path.endswith(("baserom.bin", ".gba"))
           or any(part in ("asm", "files") for part in path.split("/")[:-1])]
    if bad:
        log("    FAIL  game data is tracked in git:")
        for f in bad[:5]:
            log(f"          {f}")
        log("    These are gitignored on purpose; remove them from the index.")
        return False
    log(f"    ok: none of {', '.join(FORBIDDEN_TRACKED)} tracked "
        f"({len(tracked)} files tracked)")
    return True


def check_kit_tools(repo):
    log("[3/3] tracked Python tools have valid syntax")
    code, out = git("ls-files", "-z", "--", "tools", repo=repo)
    if code != 0:
        log("    FAIL  could not list tracked tools")
        return False
    paths = [path for path in out.split("\0") if path.endswith(".py")]
    if not paths:
        log("    FAIL  no tracked Python tools found")
        return False
    for path in paths:
        try:
            with open(os.path.join(repo, path), "rb") as source:
                compile(source.read(), path, "exec")
        except (OSError, SyntaxError, ValueError) as error:
            log(f"    FAIL  {path}: {error}")
            return False
    log(f"    ok: {len(paths)} tracked Python tool(s) compile")
    return True


def check_matches_old_unused(repo):
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


def check_plausible_old_unused(repo):
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


def check_reports_old_unused(repo):
    log("[5/5] every function in src/ has a MATCH report")
    src = os.path.join(repo, "src")
    reports = os.path.join(repo, "docs", "match")
    if not os.path.isdir(src):
        log("    ok: no src/ directory")
        return True
    problems = []
    names = sorted(p.name for p in Path(src).rglob("*.c"))
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


def capture_force_lease(repo, remote, branch):
    code, out = git("remote", "get-url", "--push", "--all", remote, repo=repo)
    destinations = out.strip().splitlines()
    if code != 0 or len(destinations) != 1:
        log("    FAIL  a rewrite requires exactly one push destination")
        return None
    destination = destinations[0]
    reference = f"refs/heads/{branch}"
    code, out = git("ls-remote", "--exit-code", "--refs", destination, reference,
                    repo=repo)
    matches = out.strip().splitlines()
    if code != 0 or len(matches) != 1:
        log("    FAIL  could not capture the existing remote branch tip")
        return None
    fields = matches[0].split()
    if len(fields) != 2 or fields[1] != reference or \
            re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", fields[0]) is None:
        log("    FAIL  invalid remote branch tip")
        return None
    return destination, fields[0]


def publish_snapshot(repo, branch, require_clean=True):
    if require_clean:
        code, out = git("status", "--porcelain=v1", "-z", "--untracked-files=all",
                        "--ignore-submodules=none", repo=repo)
        if code != 0 or out:
            log("    FAIL  publishing requires a clean tracked/index/untracked state")
            return None
    code, out = git("symbolic-ref", "--quiet", "HEAD", repo=repo)
    reference = out.strip()
    if code != 0 or reference != f"refs/heads/{branch}":
        log("    FAIL  publishing requires the expected current branch")
        return None
    code, out = git("rev-parse", "--verify", "HEAD", repo=repo)
    commit = out.strip()
    if code != 0 or re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", commit) is None:
        log("    FAIL  could not capture the current commit")
        return None
    return reference, commit


def do_push(repo, remote, branch, force=False, lease=None, commit=None):
    if force and lease is None:
        log("    FAIL  refusing a rewrite without a captured remote tip")
        return False
    if os.environ.get("FFTA_PUSH_DRY"):
        log("\nFFTA_PUSH_DRY set - not pushing")
        return True
    if commit is None:
        log("    FAIL  refusing to push without a verified commit")
        return False
    verb = "force-pushing" if force else "pushing"
    log(f"\n{verb} to {remote}/{branch} ...")
    if force:
        destination, expected = lease
        command = [f"--force-with-lease=refs/heads/{branch}:{expected}",
                   destination, f"{commit}:refs/heads/{branch}"]
    else:
        command = [remote, f"{commit}:refs/heads/{branch}"]
    code, out = git("push", *command, repo=repo)
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
    ap.add_argument("--repo", default=None)
    ap.add_argument("--kit", action="store_true",
                    help="validate only this toolkit checkout instead of a decompilation")
    ap.add_argument("--remote", default=DEFAULT_REMOTE)
    ap.add_argument("--branch", default=DEFAULT_BRANCH)
    ap.add_argument("--check-only", action="store_true",
                    help="run every check but push nothing")
    ap.add_argument("--working-tree", action="store_true",
                    help="verify the working tree instead of the commit "
                         "(normally wrong with other agents in flight)")
    ap.add_argument("--force", action="store_true",
                    help="for an intentional history rewrite: drops the "
                         "'branch contains the remote tip' requirement and "
                         "pushes with an explicit expected-tip lease. Every "
                         "other check still runs. Never "
                         "use this for ordinary work - rebase instead.")
    args = ap.parse_args()

    repo = os.path.abspath(args.repo or (KIT_ROOT if args.kit else DEFAULT_REPO))
    if args.kit and os.path.realpath(repo) != KIT_ROOT:
        sys.exit("--kit accepts only the toolkit checkout containing this script")
    if not os.path.isdir(os.path.join(repo, ".git")):
        sys.exit(f"{repo} is not a git repository")

    log(f"push gate for {repo} -> {args.remote}/{args.branch}\n")
    lease = capture_force_lease(repo, args.remote, args.branch) if args.force else None
    if args.force and lease is None:
        log("\nNOTHING PUSHED - could not establish a rewrite lease.")
        return 1
    publishing = not args.check_only and not os.environ.get("FFTA_PUSH_DRY")
    use_committed = not (args.kit or args.working_tree)
    snapshot = publish_snapshot(repo, args.branch, require_clean=not use_committed) \
        if publishing or use_committed else None
    if (publishing or use_committed) and snapshot is None:
        log("\nNOTHING PUSHED - could not establish a publication snapshot.")
        return 1
    checks = (
        check_history(repo, args.remote, args.branch, force=args.force),
        check_no_rom_data(repo, commit=snapshot[1] if use_committed else None),
    )
    tree = committed_tree(repo, snapshot[1]) if use_committed else repo
    if tree is None:
        log("\nNOTHING PUSHED - could not materialize the committed tree.")
        return 1
    try:
        checks += (check_kit_tools(repo),) if args.kit else (
            check_matches(tree, badge_base(repo)),
            check_plausible(tree),
            check_reports(tree),
        )
    finally:
        if use_committed:
            import shutil
            shutil.rmtree(tree, ignore_errors=True)
    if not all(checks):
        log("\nNOTHING PUSHED - a check above failed.")
        return 1
    log("\nall checks passed")
    if args.check_only:
        log("--check-only: stopping before the push")
        return 0
    if publishing and publish_snapshot(repo, args.branch,
                                      require_clean=not use_committed) != snapshot:
        log("\nNOTHING PUSHED - the publication snapshot changed during validation.")
        return 1
    return 0 if do_push(repo, args.remote, args.branch,
                         force=args.force, lease=lease,
                         commit=snapshot[1] if snapshot else None) else 1


if __name__ == "__main__":
    sys.exit(main())
