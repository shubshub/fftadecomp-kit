#!/usr/bin/env python3
"""
refs.py - fetch other GBA decompilations to consult before reinventing anything.

    python tools/refs.py list                  # what is in the registry, what is on disk
    python tools/refs.py sync                 # clone what is missing (shallow)
    python tools/refs.py sync --if-missing    # the same, but a no-op once populated
    python tools/refs.py sync --update        # also fetch the ones already cloned
    python tools/refs.py add owner/repo --tags gba --note "why"
    python tools/refs.py doctor               # has it ever run, is anything broken

Clones go to <state>/refs/<name>, where <state> defaults to
fftadecomp-state beside the fftadecomp repo (override with --state or
FFTA_STATE).  That directory is *outside* both repositories: reference projects
are other people's work and have no business in ours.

Why this exists: FFTA is decompiled with the same compiler family as the Pokémon
GBA games, so their struct layouts, their matching habits and their build
recipes answer questions we would otherwise burn hours guessing at - which flags
reproduce a given shape, how a struct offset is reconstructed, what a literal
pool has to look like.  Check here before spending time on a dead end.

The registry is a starting point, not gospel.  If an entry fails to clone it is
reported and left out rather than silently retried forever; extend it with
`refs.py add`, which records into refs.local.json next to this file and never
touches the committed registry.
"""

import argparse
import json
import os
import subprocess
import sys

KIT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(KIT, "tools", "refs_registry.json")
LOCAL = os.path.join(KIT, "tools", "refs.local.json")

# Curated starting point.  Every one of these is a GBA decompilation built with
# the agbcc family, which makes them the closest prior art for FFTA.
REGISTRY_SEED = [
    {"name": "pokeemerald", "repo": "pret/pokeemerald",
     "tags": ["gba", "agbcc", "matching"],
     "note": "the reference for GBA matching technique and struct layout"},
    {"name": "pokefirered", "repo": "pret/pokefirered",
     "tags": ["gba", "agbcc", "matching"],
     "note": "same compiler family; extensive per-function matching notes"},
    {"name": "pokeleafgreen", "repo": "pret/pokeleafgreen",
     "tags": ["gba", "agbcc", "matching"], "note": "Pokeblue-style, smaller codebase"},
    {"name": "pokeruby", "repo": "pret/pokeruby",
     "tags": ["gba", "agbcc", "matching"], "note": "Ruby; data-heavy, good for assets"},
    {"name": "pokesapphire", "repo": "pret/pokesapphire",
     "tags": ["gba", "agbcc", "matching"], "note": "Sapphire"},
]

for _s in ("stdout", "stderr"):
    try:
        getattr(sys, _s).reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass


def log(*a):
    print(*a, flush=True)


def state_dir(arg=None):
    root = arg or os.environ.get("FFTA_STATE")
    if root:
        return os.path.abspath(root)
    decomp = os.environ.get("FFTA_REPO")
    if not decomp:
        sibling = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(
            __file__))), "fftadecomp")
        decomp = sibling if os.path.isdir(sibling) else os.getcwd()
    return os.path.join(os.path.dirname(os.path.abspath(decomp)),
                        "fftadecomp-state")


def load_registry():
    entries = list(REGISTRY_SEED)
    path = REGISTRY
    if os.path.exists(REGISTRY):
        try:
            entries = json.load(open(REGISTRY, encoding="utf-8"))
        except (OSError, ValueError):
            log("  note: the committed registry is unreadable, using the built-in list")
    if os.path.exists(LOCAL):
        try:
            extra = json.load(open(LOCAL, encoding="utf-8"))
            known = {e["repo"] for e in entries}
            entries += [e for e in extra if e.get("repo") not in known]
        except (OSError, ValueError):
            log("  note: refs.local.json is unreadable, ignoring it")
    return entries


def run(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)


def refs_dir(arg=None):
    return os.path.join(state_dir(arg), "refs")


def git_available():
    return run(["git", "--version"]).returncode == 0


def clone(entry, dest_root, update=False):
    name = entry.get("name") or entry["repo"].split("/")[-1]
    dest = os.path.join(dest_root, name)
    if os.path.isdir(os.path.join(dest, ".git")):
        if not update:
            return "present", dest
        r = run(["git", "-C", dest, "fetch", "--depth", "1", "origin"])
        return ("updated" if r.returncode == 0 else "fetch failed"), dest
    os.makedirs(dest_root, exist_ok=True)
    r = run(["git", "clone", "--depth", "1", "--filter=blob:none",
             f"https://github.com/{entry['repo']}.git", dest])
    return ("cloned" if r.returncode == 0 else "clone failed"), dest


def cmd_list(args):
    root = refs_dir(args.state)
    log(f"reference projects -> {root}\n")
    log(f"{'name':<16}{'repo':<28}{'state':<14}tags")
    for e in load_registry():
        name = e.get("name") or e["repo"].split("/")[-1]
        dest = os.path.join(root, name)
        state = "present" if os.path.isdir(os.path.join(dest, ".git")) else "-"
        log(f"{name:<16}{e['repo']:<28}{state:<14}{', '.join(e.get('tags', []))}")
        if e.get("note"):
            log(f"{'':<16}  {e['note']}")
    return 0


def cmd_sync(args):
    if not git_available():
        log("git is not on PATH - nothing to do")
        return 1
    root = refs_dir(args.state)
    entries = load_registry()
    have = [e for e in entries
            if os.path.isdir(os.path.join(root, e.get("name")
                                          or e["repo"].split("/")[-1], ".git"))]
    if args.if_missing and have:
        log(f"{len(have)} reference project(s) already present - nothing to do")
        return 0

    log(f"syncing {len(entries)} reference project(s) into {root}\n")
    failures = []
    for e in entries:
        name = e.get("name") or e["repo"].split("/")[-1]
        state, dest = clone(e, root, update=args.update)
        log(f"  {name:<16} {state:<14} {dest}")
        if state.endswith("failed"):
            failures.append((e["repo"], (dest, state)))
    log("")
    if failures:
        log(f"{len(failures)} could not be fetched:")
        for repo, (dest, state) in failures:
            log(f"  {repo}: check the owner/name, or remove it from the registry")
        log("The rest are usable.  Reference projects are a convenience, not a "
            "dependency - carry on without the missing ones.")
        return 0                      # partial success is still success
    log(f"all {len(entries)} reference project(s) available")
    return 0


def cmd_add(args):
    if args.repo.count("/") != 1:
        sys.exit("expected owner/repo")
    entry = {"name": args.repo.split("/")[-1], "repo": args.repo,
             "tags": args.tags.split(",") if args.tags else [],
             "note": args.note or ""}
    entries = []
    if os.path.exists(LOCAL):
        entries = json.load(open(LOCAL, encoding="utf-8"))
    if any(e["repo"] == entry["repo"] for e in entries):
        log(f"{entry['repo']} is already in the local registry")
        return 0
    entries.append(entry)
    with open(LOCAL, "w", encoding="utf-8", newline="\n") as f:
        json.dump(entries, f, indent=2)
        f.write("\n")
    log(f"added {entry['repo']} to {os.path.basename(LOCAL)}")
    log("run 'refs.py sync' to fetch it")
    return 0


def cmd_doctor(args):
    root = refs_dir(args.state)
    entries = load_registry()
    log(f"state dir      {root}")
    log(f"exists         {os.path.isdir(root)}")
    present = [e for e in entries
               if os.path.isdir(os.path.join(root, e.get("name")
                                             or e["repo"].split("/")[-1], ".git"))]
    log(f"registry       {len(entries)} entr(ies)")
    log(f"present        {len(present)}")
    if not present:
        log("")
        log("The reference projects have never been fetched here.")
        log("Run:  python tools/refs.py sync")
        return 1
    log("")
    for e in present:
        name = e.get("name") or e["repo"].split("/")[-1]
        dest = os.path.join(root, name)
        r = run(["git", "-C", dest, "rev-parse", "--short", "HEAD"])
        sha = r.stdout.strip() if r.returncode == 0 else "?"
        log(f"  {name:<16} {sha:<10} {e['repo']}")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--state", default=None,
                    help="state directory (default: fftadecomp-state beside the "
                         "decomp repo, or $FFTA_STATE)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("list", help="registry and what is on disk")
    p.set_defaults(fn=cmd_list)

    p = sub.add_parser("sync", help="clone the reference projects")
    p.add_argument("--if-missing", action="store_true",
                   help="do nothing once at least one is present")
    p.add_argument("--update", action="store_true",
                   help="also fetch the ones already cloned")
    p.set_defaults(fn=cmd_sync)

    p = sub.add_parser("add", help="register another project (writes refs.local.json)")
    p.add_argument("repo")
    p.add_argument("--tags", default="")
    p.add_argument("--note", default="")
    p.set_defaults(fn=cmd_add)

    p = sub.add_parser("doctor", help="has this ever run, and what is present")
    p.set_defaults(fn=cmd_doctor)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())