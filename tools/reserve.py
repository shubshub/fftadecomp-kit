#!/usr/bin/env python3
"""
reserve.py - claim a function address before working on it, so parallel agents
do not collide.

The kit repository's issues are the ledger.  One open issue per address:

    claim 0x08011040              # reserve it (refuses if someone else has it)
    check 0x08011040              # exit 0 free, 1 taken, 3 known unmatchable
    list                          # every open reservation
    ping 0x08011040               # I am still on it (bumps the lease)
    release 0x08011040 --reason "..."
    release 0x08011040 --unmatchable --reason "no flags reproduce this"
    sweep --days 3                # close reservations nobody touched

Working agreement
-----------------
1. Before touching a function, claim it.  If the claim is refused, pick
   another address - do not work on one somebody else has.
2. A reservation is a *lease*, not a land grab: ping it while you work and
   release it as soon as you stop - including when you conclude the function
   cannot be matched.  `sweep` (and the weekly workflow) closes anything that
   has been quiet for a few days, so a stalled agent cannot hold an address.
3. `--unmatchable` also records the address in known-unmatchable.json with the
   reason and the flags tried, so the next agent does not repeat the work.

The machine-readable part of an issue lives in a marker block:

    <!-- ffareservation
    address: 0x08011040
    name: func_08011040
    size: 22
    claimed_by: some-agent
    claimed_at: 2026-10-18T06:00:00Z
    -->

Requires the gh CLI, authenticated for the kit repository.
"""

import argparse
import datetime
import json
import os
import re
import subprocess
import sys
import time

KIT_REPO = os.environ.get("FFTA_KIT_REPO", "shubshub/fftadecomp-kit")
DECOMP_REPO = os.environ.get("FFTA_REPO", "shubshub/fftadecomp")
LABEL = "reservation"
MARKER = "ffareservation"
STALE_DAYS = 3

HERE = os.path.dirname(os.path.abspath(__file__))
UNMATCHABLE_DB = os.path.join(HERE, "..", "known-unmatchable.json")

for _s in ("stdout", "stderr"):
    try:
        getattr(sys, _s).reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass


def sh(*args, check=True):
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if check and r.returncode != 0:
        sys.exit(f"gh {' '.join(args)} failed:\n{r.stderr or r.stdout}")
    return r.stdout.strip()


def ensure_label():
    try:
        sh("label", "create", LABEL, "--repo", KIT_REPO,
           "--description", "a claimed decomp address", "--color", "1d76db")
    except SystemExit:
        pass          # already there


def parse_marker(body):
    """pull the key/value block out of an issue body"""
    m = re.search(rf"<!--\s*{MARKER}(.*?)-->", body or "", re.S)
    if not m:
        return None
    out = {}
    for line in m.group(1).splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            out[k.strip()] = v.strip()
    return out


def reservations(state="open"):
    out = sh("issue", "list", "--repo", KIT_REPO, "--state", state,
             "--label", LABEL, "--limit", "200",
             "--json", "number,title,body,createdAt,updatedAt,url,author")
    items = json.loads(out or "[]")
    for it in items:
        it["meta"] = parse_marker(it.get("body")) or {}
    return items


def normalise(addr):
    return f"0x{int(str(addr), 0):08X}"


def find(addr, items=None):
    addr = normalise(addr).upper()
    for it in (items if items is not None else reservations()):
        if it["meta"].get("address", "").upper() == addr:
            return it
    return None


def unmatchable_db():
    path = os.path.abspath(UNMATCHABLE_DB)
    if not os.path.exists(path):
        return path, []
    try:
        return path, json.load(open(path, encoding="utf-8"))
    except (OSError, ValueError):
        return path, []


def function_meta(root, addr):
    """size/name from the decomp repo's analysis, when it is available"""
    cfg = os.path.join(root or ".", "config", "functions.json")
    if not os.path.exists(cfg):
        return None
    try:
        fns = json.load(open(cfg, encoding="utf-8"))
    except (OSError, ValueError):
        return None
    a = int(normalise(addr), 16)
    for f in fns:
        if int(f["rom"], 16) == a:
            return {"name": f"func_{f['rom'][2:]}",
                    "size": int(f["end"], 16) - a,
                    "mode": f.get("mode", "thumb")}
    return None


def cmd_claim(args):
    addr = normalise(args.addr)
    path, db = unmatchable_db()
    for rec in db:
        if rec["address"].upper() == addr.upper():
            print(f"{addr} is recorded as UNMATCHABLE:")
            print(f"  {rec.get('reason', 'no reason given')}")
            if rec.get("tried"):
                print(f"  flags tried: {rec['tried']}")
            print("Pick another address, or reopen the discussion on that issue.")
            return 3

    held = find(addr)
    if held:
        who = held["meta"].get("claimed_by", held["author"]["login"])
        when = held["meta"].get("claimed_at", held["createdAt"])
        print(f"{addr} is already reserved by {who} (since {when})")
        print(f"  {held['url']}")
        print("Pick another address - do not work on one somebody else holds.")
        return 1

    meta = function_meta(args.decomp_root, addr) or {}
    ensure_label()
    now = datetime.datetime.now(datetime.timezone.utc).replace(
        microsecond=0).isoformat().replace("+00:00", "Z")
    body = f"""Claiming **{addr}** before working on it.

<!-- {MARKER}
address: {addr}
name: {meta.get('name', f'func_{addr[2:]}')}
size: {meta.get('size', 'unknown')}
claimed_by: {args.who}
claimed_at: {now}
-->

Working on: {args.note or 'to be determined'}

Lease: ping with `python tools/reserve.py ping {addr}` while working, and
release with `release {addr} --reason "..."` when finished - or when the
function turns out to be unmatchable, so somebody else can pick it up.

`tools/reserve.py sweep` closes reservations quiet for {STALE_DAYS} days.
"""
    url = sh("issue", "create", "--repo", KIT_REPO,
             "--title", f"reserve: {addr} {meta.get('name', f'func_{addr[2:]}')}",
             "--body", body, "--label", LABEL)
    print(f"reserved {addr}: {url}")
    print(f"re-run   python tools/reserve.py check {addr}")
    return 0


def cmd_check(args):
    addr = normalise(args.addr)
    held = find(addr)
    if held:
        who = held["meta"].get("claimed_by", held["author"]["login"])
        print(f"TAKEN    {addr} by {who} since "
              f"{held['meta'].get('claimed_at', held['createdAt'])}")
        print(f"         {held['url']}")
        return 1
    _, db = unmatchable_db()
    for rec in db:
        if rec["address"].upper() == addr.upper():
            print(f"SKIP     {addr} recorded unmatchable: "
                  f"{rec.get('reason', '')}")
            return 3
    print(f"FREE     {addr}")
    return 0


def cmd_list(args):
    items = reservations("open")
    if not items:
        print("no open reservations")
        return 0
    now = datetime.datetime.now(datetime.timezone.utc)
    print(f"{'address':<12} {'claimed by':<18} {'age':>6}  note")
    for it in sorted(items, key=lambda x: x["meta"].get("claimed_at", "")):
        m = it["meta"]
        who = m.get("claimed_by", it["author"]["login"])
        try:
            t = datetime.datetime.fromisoformat(
                m.get("claimed_at", it["createdAt"]).replace("Z", "+00:00"))
            age = f"{(now - t).days}d"
        except ValueError:
            age = "?"
        note = m.get("note", "")
        print(f"{m.get('address', '?'):<12} {who:<18} {age:>6}  {note}")
    return 0


def cmd_ping(args):
    addr = normalise(args.addr)
    held = find(addr)
    if not held:
        print(f"{addr} is not reserved - nothing to ping", file=sys.stderr)
        return 1
    when = datetime.datetime.now(datetime.timezone.utc).isoformat()
    sh("issue", "comment", str(held["number"]), "--repo", KIT_REPO,
       "--body", f"still working on {addr} ({when})")
    print(f"pinged {addr} (#{held['number']})")
    return 0


def cmd_release(args):
    addr = normalise(args.addr)
    held = find(addr)
    if not held:
        print(f"{addr} is not reserved", file=sys.stderr)
        return 1
    reason = args.reason or "no reason given"
    sh("issue", "comment", str(held["number"]), "--repo", KIT_REPO,
       "--body", f"released {addr}: {reason}")
    sh("issue", "close", str(held["number"]), "--repo", KIT_REPO,
       "--reason", "completed" if not args.unmatchable else "not planned")
    print(f"released {addr} (#{held['number']})")

    if args.unmatchable:
        path, db = unmatchable_db()
        rec = {"address": addr, "reason": reason,
               "released_at": datetime.datetime.now(datetime.timezone.utc)
               .replace(microsecond=0).isoformat().replace("+00:00", "Z"),
               "issue": held["url"]}
        if args.tried:
            rec["tried"] = args.tried
        db = [d for d in db if d["address"].upper() != addr] + [rec]
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            json.dump(sorted(db, key=lambda d: d["address"]), f, indent=2)
            f.write("\n")
        print(f"recorded {addr} in known-unmatchable.json")
    return 0


def cmd_sweep(args):
    items = reservations("open")
    now = datetime.datetime.now(datetime.timezone.utc)
    closed = []
    for it in items:
        stamp = it.get("updatedAt") or it["createdAt"]
        try:
            t = datetime.datetime.fromisoformat(stamp.replace("Z", "+00:00"))
        except ValueError:
            continue
        days = (now - t).days
        if days < args.days:
            continue
        addr = it["meta"].get("address", it["title"])
        who = it["meta"].get("claimed_by", it["author"]["login"])
        sh("issue", "comment", str(it["number"]), "--repo", KIT_REPO,
           "--body", f"auto-released after {days} days without activity "
                     f"(lease was {STALE_DAYS} days). Claim it with "
                     f"`python tools/reserve.py claim {addr}` if you are "
                     f"still working on it.")
        sh("issue", "close", str(it["number"]), "--repo", KIT_REPO,
           "--reason", "not planned")
        closed.append((addr, who, days))
        time.sleep(0.5)
    if closed:
        print(f"auto-released {len(closed)} stale reservation(s):")
        for addr, who, days in closed:
            print(f"  {addr}  {who}  {days}d quiet")
    else:
        print(f"nothing stale (threshold {args.days} days)")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("claim", help="reserve an address")
    p.add_argument("addr")
    p.add_argument("--who", default=os.environ.get("FFTA_WHO", "agent"),
                   help="who is claiming it")
    p.add_argument("--note", default="", help="what you intend to do")
    p.add_argument("--decomp-root", default=os.environ.get("FFTA_ROOT", "."),
                   help="decomp repo, for the function's name and size")
    p.set_defaults(fn=cmd_claim)

    p = sub.add_parser("check", help="is an address free? (0 free, 1 taken, 3 unmatchable)")
    p.add_argument("addr")
    p.set_defaults(fn=cmd_check)

    p = sub.add_parser("list", help="open reservations")
    p.set_defaults(fn=cmd_list)

    p = sub.add_parser("ping", help="bump a reservation you still hold")
    p.add_argument("addr")
    p.set_defaults(fn=cmd_ping)

    p = sub.add_parser("release", help="give an address back")
    p.add_argument("addr")
    p.add_argument("--reason", default="")
    p.add_argument("--unmatchable", action="store_true",
                   help="also record it in known-unmatchable.json")
    p.add_argument("--tried", default="", help="flags/settings already tried")
    p.set_defaults(fn=cmd_release)

    p = sub.add_parser("sweep", help="close reservations nobody touched")
    p.add_argument("--days", type=int, default=STALE_DAYS)
    p.set_defaults(fn=cmd_sweep)

    args = ap.parse_args()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())