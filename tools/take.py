#!/usr/bin/env python3
"""
take.py - the official way to reserve a decomp address before working on it.

    python tools/take.py check  0x0814860C        # is it free?
    python tools/take.py claim  0x0814860C --who me --note "leaf, 32 B"
    python tools/take.py list
    python tools/take.py ping   0x0814860C        # still on it, bumps the lease
    python tools/take.py release 0x0814860C --reason "matched, in src/"
    python tools/take.py release 0x0814860C --unmatchable --reason "..." --tried "..."
    python tools/take.py sweep  --days 3          # drop rows nobody touched
    python tools/take.py doctor                   # is the ledger healthy?

Why this exists
---------------
`reserve.py` is a *client* for the broker workflow: it posts a request comment
and the workflow turns it into an accepted row.  That is the right shape when
the workflow is draining, but it means a claim is asynchronous and can sit
"submitted, not yet accepted" indefinitely - so an agent can believe it holds
an address when it does not.  This tool writes the ledger itself, in the same
schema the broker reads, and confirms the write survived.

It refuses, before writing anything:

  1. an address already reserved            (exit 1)
  2. an address recorded unmatchable        (exit 3)
  3. an address already matched in src/     (exit 4)
  4. an address matched in an open PR       (exit 5)
  5. a dirty or unparseable ledger          (exit 2)
  6. while broker requests are pending      (exit 7) - never race the broker
and re-reads after writing: if the row is not there, somebody else won the
race and this exits 8 rather than pretending it holds the lease.

Exit codes: 0 ok, 1 taken, 2 bad ledger, 3 unmatchable, 4 matched, 5 in a PR,
6 unconfirmed, 7 broker busy, 8 lost race, 9 usage.

Requires the gh CLI, authenticated for the kit repository.
"""

import argparse
import datetime
import json
import os
import re
import subprocess
import sys

KIT_REPO = os.environ.get("FFTA_KIT_REPO", "shubshub/fftadecomp-kit")
DECOMP_REPO = os.environ.get("FFTA_REPO", "shubshub/fftadecomp")
LEDGER_TITLE = os.environ.get("FFTA_LEDGER_TITLE", "address ledger").lower()
STATE_START = "<!-- ffta-ledger-state\n"
STATE_END = "\nffta-ledger-state -->"
TABLE_START = "<!-- ffta-ledger:start -->"
TABLE_END = "<!-- ffta-ledger:end -->"
REQUEST_MARK = "ffta-reservation-request:v1"
RESULT_MARK = "ffta-ledger-result"
STALE_DAYS = 3

EXIT_OK, EXIT_TAKEN, EXIT_LEDGER, EXIT_UNMATCHABLE = 0, 1, 2, 3
EXIT_MATCHED, EXIT_UNCONFIRMED, EXIT_BUSY, EXIT_RACE = 4, 5, 7, 8

HERE = os.path.dirname(os.path.abspath(__file__))
UNMATCHABLE_DB = os.path.join(HERE, "..", "known-unmatchable.json")

for _s in ("stdout", "stderr"):
    try:
        getattr(sys, _s).reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass


class GhError(SystemExit):
    """gh failed; .text is the message, .permission is True if it was a 403

    SystemExit, not RuntimeError, on purpose: this used to be a plain
    sys.exit(), and the callers that tolerate a failed read - a 404 for
    'src/<addr>.c does not exist' is the normal answer for an unmatched
    function - catch SystemExit.  Deriving from it keeps them working, while
    the more specific 'except GhError' handlers added here still win.
    """

    def __init__(self, message, permission=False):
        super().__init__(message)
        self.text = message
        self.permission = permission


def gh(*args, stdin=None, check=True):
    r = subprocess.run(["gh", *args], input=stdin, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    if check and r.returncode != 0:
        message = (r.stderr or r.stdout or "").strip()
        low = message.lower()
        permission = ("403" in message or "resource not accessible" in low or
                      "must have write access" in low or
                      "permission denied" in low or "not allowed" in low)
        raise GhError(f"gh {' '.join(args[:3])} failed:\n{message}", permission)
    return r


def now():
    return datetime.datetime.now(datetime.timezone.utc).replace(
        microsecond=0).isoformat().replace("+00:00", "Z")


def normalise(addr):
    return f"0x{int(str(addr), 0):08X}"


def parse_ts(ts):
    try:
        return datetime.datetime.fromisoformat(str(ts).replace("Z", "+00:00"))
    except (ValueError, TypeError):
        return None


# --------------------------------------------------------------- ledger I/O

def ledger_number():
    override = os.environ.get("FFTA_LEDGER_ISSUE")
    if override and override.isdigit():
        return int(override)
    issues = json.loads(gh("issue", "list", "--repo", KIT_REPO, "--state", "open",
                          "--limit", "50", "--json", "number,title").stdout or "[]")
    for issue in issues:
        if str(issue.get("title", "")).strip().lower() == LEDGER_TITLE:
            return int(issue["number"])
    return 0


def fetch_ledger():
    """returns (number, state) or raises RuntimeError with a readable reason"""
    number = ledger_number()
    if not number:
        raise RuntimeError(
            f"no open issue titled '{LEDGER_TITLE}' in {KIT_REPO} "
            f"(set FFTA_LEDGER_ISSUE=<n> to pin one)")
    issue = json.loads(gh("api", f"repos/{KIT_REPO}/issues/{number}").stdout)
    if issue.get("pull_request"):
        raise RuntimeError(f"issue #{number} is a pull request, not a ledger")
    if issue.get("state") != "open":
        raise RuntimeError(f"ledger #{number} is {issue.get('state')}, not open")
    body = issue.get("body") or ""
    if "\r" in body:
        raise RuntimeError(f"ledger #{number} body has CRLF line endings; "
                           f"the state markers will not parse")
    if body.count(STATE_START) != 1 or body.count(STATE_END) != 1:
        raise RuntimeError(f"ledger #{number} state markers missing or ambiguous")
    blob = body.split(STATE_START, 1)[1].split(STATE_END, 1)[0].strip()
    try:
        state = json.loads(blob)
    except ValueError as exc:
        raise RuntimeError(f"ledger #{number} state is not valid JSON: {exc}")
    if not isinstance(state.get("rows"), list):
        raise RuntimeError(f"ledger #{number} state has no rows list")
    return number, state


def render(state):
    head = ["# Address ledger", "",
            "Reservations are leases. Claim with `tools/take.py claim <addr>`;",
            "release them when you stop, including when a function turns out to",
            "be unmatchable. Rows quiet for 3 days are swept.", "",
            TABLE_START,
            "| address | claimed by | claimed at | last seen | note |",
            "|---|---|---|---|---|"]
    for row in state["rows"]:
        cells = [str(row.get(f, "")).replace("|", r"\|")
                 for f in ("address", "who", "claimed_at", "last_seen", "note")]
        head.append("| " + " | ".join(cells) + " |")
    meta = json.dumps(state, ensure_ascii=True, separators=(",", ":")) \
        .replace("<", r"\<").replace(">", r"\>")
    return "\n".join(head + [TABLE_END, "", STATE_START + meta + STATE_END, ""])


def write_ledger(number, state):
    """write the body through a file - stdin would gain CRLF on Windows

    This edits the ledger issue's *body*, so it needs write access on the
    issue: being the author, or having triage/write permission on the repo.
    A third party can comment on a public issue but cannot edit its body, and
    GitHub answers that with a 403.  cmd_claim catches that and routes to the
    broker request instead.
    """
    body = render(state)
    if "\r" in body:
        raise RuntimeError("refusing to write: rendered body contains CR")
    path = os.path.join(os.environ.get("TEMP", "/tmp"), "ffta-ledger-body.md")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(body)
    gh("issue", "edit", str(number), "--repo", KIT_REPO, "--body-file", path)
    os.remove(path)


def comment(number, text):
    try:
        gh("issue", "comment", str(number), "--repo", KIT_REPO, "--body", text)
    except SystemExit:
        pass


def pending_requests(number, state=None):
    """broker request comments that have not been answered yet

    The broker records its answers in the ledger body, in state["results"] -
    not as comments.  This used to look for a 'ffta-ledger-result' comment that
    the broker never writes, so every request ever submitted stayed pending
    forever and the tool refused to write anything: 'the broker has N
    unanswered request(s)'.  A third party hit exactly that, because they can
    comment on the ledger but cannot edit its body.
    """
    items = json.loads(gh("api", f"repos/{KIT_REPO}/issues/{number}/comments",
                         "--paginate").stdout or "[]")
    asked, done = set(), set()
    for c in items:
        b = c.get("body") or ""
        m = re.search(r"\{.*\}", b, re.S)
        if not m:
            continue
        try:
            payload = json.loads(m.group(0))
        except ValueError:
            continue
        if REQUEST_MARK in b and payload.get("operation"):
            key = (payload.get("operation"), str(payload.get("address", "")).upper())
            asked.add(key)
        if RESULT_MARK in b:
            addr = str(payload.get("address", "")).upper()
            done.add(addr)
    # the broker's own answers live in the ledger body
    if state is not None:
        for result in state.get("results", []):
            addr = result.get("address")
            if addr:
                done.add(str(addr).upper())
    return sorted(key for key in asked if key[1] not in done)


# ------------------------------------------------------------ other sources

def unmatchable_db():
    path = os.path.abspath(UNMATCHABLE_DB)
    if not os.path.exists(path):
        return path, []
    try:
        return path, json.load(open(path, encoding="utf-8"))
    except (OSError, ValueError):
        return path, []


def already_matched(addr, decomp_root=None):
    root = decomp_root or os.environ.get("FFTA_ROOT") or "."
    if os.path.exists(os.path.join(root, "src", addr[2:] + ".c")):
        return True
    try:
        out = gh("api",
                 f"repos/{DECOMP_REPO}/contents/src/{addr[2:]}.c").stdout
        return bool(out) and '"path"' in out
    except SystemExit:
        return False


def in_open_pr(addr):
    try:
        prs = json.loads(gh("pr", "list", "--repo", DECOMP_REPO, "--state", "open",
                            "--limit", "100", "--json", "number,title,body",
                            "url").stdout or "[]")
    except SystemExit:
        return []
    a1, a2 = addr.lower(), addr[2:].lower()
    return [pr for pr in prs
            if a1 in f"{pr.get('title','')}\n{pr.get('body') or ''}".lower()
            or a2 in f"{pr.get('title','')}\n{pr.get('body') or ''}".lower()]


def held_by(state, addr):
    return next((r for r in state["rows"]
                 if str(r.get("address", "")).upper() == addr.upper()), None)


# --------------------------------------------------------------- the commands

def cmd_check(args):
    addr = normalise(args.addr)
    try:
        _, state = fetch_ledger()
    except RuntimeError as exc:
        print(f"LEDGER ERROR: {exc}")
        return EXIT_LEDGER
    row = held_by(state, addr)
    if row:
        print(f"TAKEN    {addr} by {row.get('who')} "
              f"since {row.get('claimed_at')} (last seen {row.get('last_seen')})")
        return EXIT_TAKEN
    _, db = unmatchable_db()
    if any(d.get("address", "").upper() == addr.upper() for d in db):
        print(f"SKIP     {addr} recorded unmatchable")
        return EXIT_UNMATCHABLE
    if already_matched(addr):
        print(f"MATCHED  {addr} already in src/ - nothing to claim")
        return EXIT_MATCHED
    prs = in_open_pr(addr)
    if prs:
        print(f"IN PR    {addr} is being matched in open PR(s):")
        for pr in prs:
            print(f"         #{pr['number']}  {pr['title']}")
        return EXIT_MATCHED
    print(f"FREE     {addr}")
    return EXIT_OK


def broker_request(args, addr, row=None):
    """post a request comment and wait for the workflow to accept it

    The reservations workflow runs with issues: write on the kit repository,
    so it can edit the ledger body on a third party's behalf.  That is the
    only path that works for someone without write access.
    """
    import json as _json
    request = {"operation": args.cmd, "address": addr,
               "who": getattr(args, "who", None) or "agent"}
    if args.cmd == "claim":
        request["note"] = getattr(args, "note", "") or "-"
    else:
        # ping and release are bound to the original claim generation
        claim_id = (row or {}).get("claim_id")
        if claim_id is None:
            print("this lease has no claim generation, so the broker cannot "
                  "match the request to it.")
            print("Ask a maintainer to reconcile the row.")
            return EXIT_UNCONFIRMED
        request["claim_id"] = claim_id
        request["reason"] = getattr(args, "reason", "") or ""
        request["unmatchable"] = bool(getattr(args, "unmatchable", False))
        tried = getattr(args, "tried", "")
        if tried:
            request["tried"] = tried
    body = ("<!-- ffta-reservation-request:v1 -->\n" +
            _json.dumps(request, ensure_ascii=True, separators=(",", ":")))
    try:
        comment_number, _ = fetch_ledger()
        comment(comment_number, body)
    except GhError as exc:
        print(f"could not submit the request: {exc}")
        print("Check that 'gh' is installed and authenticated with a token "
              "that can comment on public issues (scope: repo).")
        return EXIT_UNCONFIRMED
    print(f"request submitted to ledger #{comment_number}; it is not accepted "
          f"yet.")
    print("Do not start work until it is accepted - poll with "
          f"'take.py list'.")
    return EXIT_UNCONFIRMED


def cmd_claim(args):
    addr = normalise(args.addr)
    code = cmd_check(args)
    if code != EXIT_OK:
        return code
    number, state = fetch_ledger()
    busy = pending_requests(number, state)
    if busy:
        print(f"REFUSING to write: the broker has {len(busy)} unanswered "
              f"request(s) ({', '.join(op + ' ' + a for op, a in busy[:4])}).")
        print("Run 'take.py doctor' to see them; clear with "
              "'take.py purge-requests' before writing.")
        return EXIT_BUSY
    ts = now()
    row = {"address": addr, "who": args.who, "claimed_at": ts,
           "last_seen": ts, "note": args.note or "-",
           "owner_id": None, "claim_id": None}
    state["rows"].append(row)
    try:
        write_ledger(number, state)
    except GhError as exc:
        if not exc.permission:
            print(f"write failed: {exc}")
            return EXIT_UNCONFIRMED
        # No write access on the issue body - which is the normal case for
        # anyone but the maintainer.  Posting a request comment needs no write
        # access, and the reservations workflow applies it on our behalf.
        print("cannot edit the ledger issue body (no write access on the "
              "issue).")
        print("submitting a broker request instead - the reservations "
              "workflow will apply it.")
        return broker_request(args, addr, row)
    except RuntimeError as exc:
        print(f"write failed: {exc}")
        return EXIT_UNCONFIRMED
    _, check = fetch_ledger()          # confirm the lease really took
    if not held_by(check, addr):
        print(f"lost the race for {addr} - someone else holds it now")
        return EXIT_RACE
    comment(number, f"**claimed {addr}** by `{args.who}` — {row['note']}")
    print(f"reserved {addr}  (ledger #{number})")
    print(f"  {row['note']}")
    return EXIT_OK


def cmd_ping(args):
    addr = normalise(args.addr)
    number, state = fetch_ledger()
    row = held_by(state, addr)
    if not row:
        print(f"{addr} is not reserved by this ledger", file=sys.stderr)
        return EXIT_TAKEN
    row["last_seen"] = now()
    try:
        write_ledger(number, state)
    except GhError as exc:
        if not exc.permission:
            print(f"write failed: {exc}")
            return EXIT_UNCONFIRMED
        print("cannot edit the ledger issue body (no write access on the "
              "issue); submitting a broker request instead.")
        return broker_request(args, addr, row)
    comment(number, f"lease refreshed on {addr} by `{row.get('who')}`")
    print(f"pinged {addr}")
    return EXIT_OK


def cmd_release(args):
    addr = normalise(args.addr)
    number, state = fetch_ledger()
    row = held_by(state, addr)
    if not row:
        print(f"{addr} is not reserved", file=sys.stderr)
        return EXIT_TAKEN
    state["rows"] = [r for r in state["rows"]
                     if str(r.get("address", "")).upper() != addr.upper()]
    try:
        write_ledger(number, state)
    except GhError as exc:
        if not exc.permission:
            print(f"write failed: {exc}")
            return EXIT_UNCONFIRMED
        print("cannot edit the ledger issue body (no write access on the "
              "issue); submitting a broker request instead.")
        return broker_request(args, addr, row)
    except RuntimeError as exc:
        print(f"write failed: {exc}")
        return EXIT_UNCONFIRMED
    reason = args.reason or "no reason given"
    comment(number, f"**released {addr}** (was `{row.get('who')}`): {reason}")
    print(f"released {addr}")
    if args.unmatchable:
        path, db = unmatchable_db()
        rec = {"address": addr, "reason": reason, "released_at": now(),
               "who": row.get("who")}
        if args.tried:
            rec["tried"] = args.tried
        db = [d for d in db if d.get("address", "").upper() != addr.upper()] + [rec]
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            json.dump(sorted(db, key=lambda d: d["address"]), f, indent=2)
            f.write("\n")
        print(f"recorded {addr} in known-unmatchable.json")
    return EXIT_OK


def cmd_list(args):
    try:
        number, state = fetch_ledger()
    except RuntimeError as exc:
        print(f"LEDGER ERROR: {exc}")
        return EXIT_LEDGER
    rows = sorted(state["rows"], key=lambda r: str(r.get("address")))
    if not rows:
        print(f"no reservations (ledger #{number})")
        return EXIT_OK
    now_ = datetime.datetime.now(datetime.timezone.utc)
    print(f"{'address':<12} {'claimed by':<16} {'age':>4}  note")
    for r in rows:
        t = parse_ts(r.get("last_seen"))
        age = f"{(now_ - t).days}d" if t else "?"
        flag = "  <- STALE" if t and (now_ - t).days >= STALE_DAYS else ""
        print(f"{r.get('address',''):<12} {str(r.get('who',''))[:16]:<16} "
              f"{age:>4}  {r.get('note','')}{flag}")
    print(f"\nledger #{number}")
    return EXIT_OK


def cmd_sweep(args):
    number, state = fetch_ledger()
    now_ = datetime.datetime.now(datetime.timezone.utc)
    keep, dropped = [], []
    for r in state["rows"]:
        t = parse_ts(r.get("last_seen"))
        (dropped if t and (now_ - t).days >= args.days else keep).append(r)
    if not dropped:
        print(f"nothing stale (threshold {args.days} days)")
        return EXIT_OK
    state["rows"] = keep
    write_ledger(number, state)
    lines = [f"**swept {len(dropped)} stale reservation(s)** "
             f"(threshold {args.days} days):", ""]
    for r in dropped:
        lines.append(f"- `{r.get('address')}` held by `{r.get('who')}`, "
                     f"last seen {r.get('last_seen')}")
    comment(number, "\n".join(lines))
    print(f"dropped {len(dropped)}: " +
          ", ".join(str(r.get("address")) for r in dropped))
    return EXIT_OK


def cmd_note_unmatchable(args):
    """record a dead end without a live lease (after release, or from a park note)"""
    addr = normalise(args.addr)
    number, state = fetch_ledger()
    if held_by(state, addr):
        sys.exit(f"{addr} is still reserved - release it with --unmatchable so "
                 f"the reason lands on the reservation")
    path, db = unmatchable_db()
    rec = {"address": addr, "reason": args.reason or "no reason given",
           "released_at": now(), "who": args.who}
    if args.tried:
        rec["tried"] = args.tried
    db = [d for d in db if d.get("address", "").upper() != addr.upper()] + [rec]
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        json.dump(sorted(db, key=lambda d: d["address"]), f, indent=2)
        f.write("\n")
    comment(number,
            f"**recorded {addr} as unmatchable** (no lease needed): "
            f"{rec['reason']}")
    print(f"recorded {addr} in known-unmatchable.json")
    return 0


def cmd_doctor(args):
    try:
        number, state = fetch_ledger()
    except RuntimeError as exc:
        print(f"UNHEALTHY: {exc}")
        return EXIT_LEDGER
    print(f"ledger            #{number}  (open, parseable)")
    print(f"rows              {len(state['rows'])}")
    print(f"broker cursor     {state.get('cursor')}")
    pending = pending_requests(number)
    if pending:
        print(f"pending requests  {len(pending)}")
        for op, a in pending:
            print(f"    {op} {a}")
        print("  -> claims will be REFUSED until these are answered or purged")
    else:
        print("pending requests  0")
    now_ = datetime.datetime.now(datetime.timezone.utc)
    for r in state["rows"]:
        t = parse_ts(r.get("last_seen"))
        if t and (now_ - t).days >= STALE_DAYS:
            print(f"    stale: {r.get('address')} ({r.get('who')})")
    return EXIT_OK


def cmd_purge(args):
    number = ledger_number()
    items = json.loads(gh("api", f"repos/{KIT_REPO}/issues/{number}/comments",
                         "--paginate").stdout or "[]")
    n = 0
    for c in items:
        if REQUEST_MARK in (c.get("body") or ""):
            gh("api", "-X", "DELETE",
               f"repos/{KIT_REPO}/issues/comments/{c['id']}")
            n += 1
    print(f"deleted {n} pending request comment(s) from ledger #{number}")
    return EXIT_OK


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("check", help="is an address free to work on?")
    p.add_argument("addr")
    p.set_defaults(fn=cmd_check)

    p = sub.add_parser("claim", help="reserve an address (writes the ledger)")
    p.add_argument("addr")
    p.add_argument("--who", default=os.environ.get("FFTA_WHO", "agent"))
    p.add_argument("--note", default="")
    p.set_defaults(fn=cmd_claim)

    p = sub.add_parser("list", help="show the ledger")
    p.set_defaults(fn=cmd_list)

    p = sub.add_parser("ping", help="bump the lease on something you hold")
    p.add_argument("addr")
    p.set_defaults(fn=cmd_ping)

    p = sub.add_parser("release", help="give an address back")
    p.add_argument("addr")
    p.add_argument("--reason", default="")
    p.add_argument("--unmatchable", action="store_true",
                   help="also record it in known-unmatchable.json")
    p.add_argument("--tried", default="")
    p.set_defaults(fn=cmd_release)

    p = sub.add_parser("sweep", help="drop rows nobody has touched")
    p.add_argument("--days", type=int, default=STALE_DAYS)
    p.set_defaults(fn=cmd_sweep)

    p = sub.add_parser("note-unmatchable",
                       help="record a dead end for an address that is not reserved")
    p.add_argument("addr")
    p.add_argument("--reason", default="")
    p.add_argument("--tried", default="")
    p.add_argument("--who", default=os.environ.get("FFTA_WHO", "agent"))
    p.set_defaults(fn=cmd_note_unmatchable)

    p = sub.add_parser("doctor", help="is the ledger healthy?")
    p.set_defaults(fn=cmd_doctor)

    p = sub.add_parser("purge-requests",
                       help="delete unanswered broker requests (maintainer)")
    p.set_defaults(fn=cmd_purge)

    args = ap.parse_args()
    try:
        return args.fn(args)
    except GhError as exc:
        # gh() used to exit with a plain message; keep it that way, and say
        # what a permission failure means, because it is the single most
        # common way for a new contributor to get stuck.
        print(str(exc), file=sys.stderr)
        if exc.permission:
            print("GitHub refused the write.  If this is the ledger issue, "
                  "the usual cause is editing an issue body you do not own: "
                  "commenting on a public issue is allowed, editing it needs "
                  "write access.", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())