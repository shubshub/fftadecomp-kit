#!/usr/bin/env python3
"""
reserve.py - claim a function address before working on it, so parallel agents
do not collide.

The kit repository has ONE issue that is the ledger, and every reservation is a
row in it.  One issue means one place to look, one thing to subscribe to, and
no issue-list noise as the project grows.

    claim 0x08011040              # reserve it (refuses if somebody holds it)
    check 0x08011040              # exit 0 free, 1 taken, 3 known unmatchable
    list                          # the whole ledger
    ping 0x08011040               # still on it; refreshes the lease
    release 0x08011040 --reason "..."
    release 0x08011040 --unmatchable --reason "no flags reproduce this"
    sweep --days 3                # drop rows nobody has touched

Working agreement
-----------------
1. Before touching a function, claim it.  If the claim is refused, pick another
   address - do not work on one somebody else holds.
2. A reservation is a *lease*: ping it while you work and release it as soon as
   you stop - including when you conclude the function cannot be matched.
   `sweep` (and the reservations workflow) drops rows quiet for a few days.
3. `--unmatchable` also records the address in known-unmatchable.json with the
   reason and the flags tried, so the next agent does not repeat the dead end.

Every claim and release is also posted as a comment on the ledger, so the audit
trail survives rows being removed.

The machine-readable part of the ledger is the table between the markers:

    <!-- ffta-ledger:start -->
    | address | claimed by | claimed at | last seen | note |
    |---|---|---|---|---|
    | 0x08011040 | opencode | 2026-10-18T05:43:46Z | 2026-10-18T06:10:00Z | ... |
    <!-- ffta-ledger:end -->

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
LEDGER_TITLE = os.environ.get("FFTA_LEDGER_TITLE", "address ledger")
START = "<!-- ffta-ledger:start -->"
END = "<!-- ffta-ledger:end -->"
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


def self_update(quiet=False):
    """pull the latest kit before touching the ledger.

    The ledger itself lives on GitHub and is always current, but
    known-unmatchable.json and this script's logic live in the checkout - a
    stale kit means a stale view of what is known-unmatchable and an old
    claim/release implementation.  So every command refreshes first.
    """
    repo = os.path.dirname(os.path.abspath(HERE))
    if not os.path.isdir(os.path.join(repo, ".git")):
        return False
    r = subprocess.run(["git", "-C", repo, "pull", "--ff-only", "-q"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        if not quiet:
            print(f"note: could not update {repo} ({r.stderr.strip() or 'not a git checkout'}); "
                  f"continuing with the local copy", file=sys.stderr)
        return False
    if not quiet and r.stdout.strip():
        print(f"updated kit from origin: {r.stdout.strip()}")
    return True


def now():
    return datetime.datetime.now(datetime.timezone.utc).replace(
        microsecond=0).isoformat().replace("+00:00", "Z")


def parse_ts(ts):
    try:
        return datetime.datetime.fromisoformat(ts.replace("Z", "+00:00"))
    except (ValueError, AttributeError):
        return None


def age_days(ts):
    t = parse_ts(ts)
    return None if t is None else (
        datetime.datetime.now(datetime.timezone.utc) - t).days


# ---------------------------------------------------------------- ledger ---

def normalise(addr):
    return f"0x{int(str(addr), 0):08X}"


def ledger(create=False):
    """the one issue that holds the table"""
    items = json.loads(sh("issue", "list", "--repo", KIT_REPO, "--state", "open",
                          "--limit", "100", "--json", "number,title,body,url",
                          check=False) or "[]")
    for it in items:
        if it["title"].strip().lower() == LEDGER_TITLE.lower():
            return it
    if not create:
        return None
    url = sh("issue", "create", "--repo", KIT_REPO,
             "--title", LEDGER_TITLE, "--body", render([]))
    number = int(re.search(r"/issues/(\d+)", url).group(1))
    pin(number)
    return {"number": number, "title": LEDGER_TITLE,
            "body": render([]), "url": url}


def pin(number):
    """best effort: pinned issues are the first thing anybody sees"""
    r = subprocess.run(
        ["gh", "api", "graphql", "-f",
         "query=mutation($id:ID!){addPinToIssue(input:{issueId:$id})"
         "{clientMutationId}}",
         "-F", f"id=Issue:{number}"],
        capture_output=True, text=True)
    return r.returncode == 0


def rows_of(body):
    m = re.search(re.escape(START) + r"(.*?)" + re.escape(END), body or "", re.S)
    if not m:
        return []
    out = []
    for line in m.group(1).splitlines():
        if not line.strip().startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 5 or not cells[0].lower().startswith("0x"):
            continue                       # header or separator
        out.append({"address": normalise(cells[0]), "who": cells[1],
                    "claimed_at": cells[2], "last_seen": cells[3],
                    "note": cells[4] if len(cells) > 4 else ""})
    return out


def render(rows):
    head = [
        "# Address ledger",
        "",
        "Every decomp address somebody is working on, in one place. One row per",
        "address; a row that goes quiet for 3 days is dropped automatically, so",
        "an agent that stops working does not keep an address hostage.",
        "",
        "```sh",
        f"python tools/reserve.py check 0x08011040     # 0 free, 1 taken, 3 unmatchable",
        f"python tools/reserve.py claim 0x08011040 --who <you> --note \"...\"",
        f"python tools/reserve.py ping 0x08011040      # still on it",
        f"python tools/reserve.py release 0x08011040 --reason \"...\"",
        f"python tools/reserve.py release 0x08011040 --unmatchable --reason \"...\" --tried \"...\"",
        "```",
        "",
        "Claim before you touch a function. If a claim is refused, that address",
        "belongs to another agent - pick a different one.",
        "",
        START,
        "| address | claimed by | claimed at | last seen | note |",
        "|---|---|---|---|---|",
    ]
    body = [f"| {r['address']} | {r['who']} | {r['claimed_at']} | "
            f"{r['last_seen']} | {r['note']} |" for r in rows]
    return "\n".join(head + body + [END, ""])


def write(rows, comment=None):
    led = ledger(create=True)
    sh("issue", "edit", str(led["number"]), "--repo", KIT_REPO,
       "--body", render(rows))
    if comment:
        sh("issue", "comment", str(led["number"]), "--repo", KIT_REPO,
           "--body", comment)
    return led


def held_by(rows, addr):
    addr = normalise(addr).upper()
    for r in rows:
        if r["address"].upper() == addr:
            return r
    return None


# ------------------------------------------------------------ the commands --

def function_meta(root, addr):
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
                    "size": int(f["end"], 16) - a}
    return None


def unmatchable_db():
    path = os.path.abspath(UNMATCHABLE_DB)
    if not os.path.exists(path):
        return path, []
    try:
        return path, json.load(open(path, encoding="utf-8"))
    except (OSError, ValueError):
        return path, []


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

    led = ledger(create=True)
    rows = rows_of(led["body"])
    existing = held_by(rows, addr)
    if existing:
        print(f"{addr} is already reserved by {existing['who']} "
              f"(since {existing['claimed_at']})")
        print(f"  ledger: {led['url']}")
        print("Pick another address - do not work on one somebody else holds.")
        return 1

    meta = function_meta(args.decomp_root, addr) or {}
    ts = now()
    note = " ".join(filter(None, [
        args.note,
        f"[{meta.get('size', '?')} B]" if meta.get("size") else "",
    ]))
    rows.append({"address": addr, "who": args.who, "claimed_at": ts,
                 "last_seen": ts, "note": note or "-"})
    write(rows, f"**claimed {addr}** by `{args.who}` "
                f"({meta.get('name', '')}). {note}")
    print(f"reserved {addr} ({meta.get('name', '')})")
    print(f"ledger:  {led['url']}")
    return 0


def cmd_check(args):
    addr = normalise(args.addr)
    led = ledger()
    if led:
        row = held_by(rows_of(led["body"]), addr)
        if row:
            print(f"TAKEN    {addr} by {row['who']} since {row['claimed_at']}"
                  f" (last seen {row['last_seen']})")
            print(f"         {led['url']}")
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
    led = ledger()
    if not led:
        print("no ledger issue yet - claim something to create it")
        return 0
    rows = rows_of(led["body"])
    if not rows:
        print("no reservations")
        return 0
    print(f"{'address':<12} {'claimed by':<16} {'age':>4}  note")
    for r in rows:
        age = age_days(r["last_seen"])
        flag = "  <- stale" if age is not None and age >= STALE_DAYS else ""
        print(f"{r['address']:<12} {r['who']:<16} {age if age is not None else '?':>4}"
              f"  {r['note']}{flag}")
    print(f"\n{led['url']}")
    return 0


def cmd_ping(args):
    addr = normalise(args.addr)
    led = ledger(create=True)
    rows = rows_of(led["body"])
    row = held_by(rows, addr)
    if not row:
        print(f"{addr} is not reserved", file=sys.stderr)
        return 1
    row["last_seen"] = now()
    write(rows, f"still working on {addr} (`{row['who']}`) - lease refreshed")
    print(f"pinged {addr}")
    return 0


def cmd_release(args):
    addr = normalise(args.addr)
    led = ledger(create=True)
    rows = rows_of(led["body"])
    row = held_by(rows, addr)
    if not row:
        print(f"{addr} is not reserved", file=sys.stderr)
        return 1
    reason = args.reason or "no reason given"
    rows = [r for r in rows if r["address"].upper() != addr.upper()]
    write(rows, f"**released {addr}** (was `{row['who']}`): {reason}")
    print(f"released {addr} (was {row['who']})")

    if args.unmatchable:
        path, db = unmatchable_db()
        rec = {"address": addr, "reason": reason, "released_at": now(),
               "who": row["who"]}
        if args.tried:
            rec["tried"] = args.tried
        db = [d for d in db if d["address"].upper() != addr.upper()] + [rec]
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            json.dump(sorted(db, key=lambda d: d["address"]), f, indent=2)
            f.write("\n")
        print(f"recorded {addr} in known-unmatchable.json")
    return 0


def cmd_sweep(args):
    led = ledger()
    if not led:
        print("no ledger yet")
        return 0
    rows = rows_of(led["body"])
    dropped = []
    keep = []
    for r in rows:
        age = age_days(r["last_seen"])
        if age is not None and age >= args.days:
            dropped.append((r, age))
        else:
            keep.append(r)
    if not dropped:
        print(f"nothing stale (threshold {args.days} days)")
        return 0
    summary = "\n".join(
        f"- **{r['address']}** dropped, held by `{r['who']}` for {age} days "
        f"without activity" for r, age in dropped)
    write(keep, f"**swept {len(dropped)} stale reservation(s)** "
                f"(threshold {args.days} days):\n\n{summary}")
    print(f"dropped {len(dropped)} stale reservation(s):")
    for r, age in dropped:
        print(f"  {r['address']}  {r['who']}  {age}d quiet")
    time.sleep(0.2)
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("claim", help="reserve an address")
    p.add_argument("addr")
    p.add_argument("--who", default=os.environ.get("FFTA_WHO", "agent"))
    p.add_argument("--note", default="", help="what you intend to do")
    p.add_argument("--decomp-root", default=os.environ.get("FFTA_ROOT", "."))
    p.set_defaults(fn=cmd_claim)

    p = sub.add_parser("check", help="is an address free? (0 free, 1 taken, 3 unmatchable)")
    p.add_argument("addr")
    p.set_defaults(fn=cmd_check)

    p = sub.add_parser("list", help="the whole ledger")
    p.set_defaults(fn=cmd_list)

    p = sub.add_parser("ping", help="refresh a reservation you still hold")
    p.add_argument("addr")
    p.set_defaults(fn=cmd_ping)

    p = sub.add_parser("release", help="give an address back")
    p.add_argument("addr")
    p.add_argument("--reason", default="")
    p.add_argument("--unmatchable", action="store_true")
    p.add_argument("--tried", default="", help="flags/settings already tried")
    p.set_defaults(fn=cmd_release)

    p = sub.add_parser("sweep", help="drop rows nobody has touched")
    p.add_argument("--days", type=int, default=STALE_DAYS)
    p.set_defaults(fn=cmd_sweep)

    ap.add_argument("--no-pull", action="store_true",
                    help="skip the automatic 'git pull' of this repo")
    args = ap.parse_args()
    if not args.no_pull:
        self_update()
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())