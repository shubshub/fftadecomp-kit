"""Reserve many addresses in one ledger write.

take.py claims one address at a time, and each claim is a full read of the
ledger issue, an edit of its body, and a re-read to confirm.  For a batch of
sixty-four that is two hundred GitHub round trips, and every one of them is a
chance for somebody else's claim to land in between.

This does the same work in one pass: read the ledger once, decide on every
address against the same rules cmd_check applies - not held, not recorded
unmatchable, not already matched in src/, not being matched in an open pull
request - add the rows, write the body once, then re-read and confirm that
every row really took.  If the write is refused, nothing is claimed at all.

    python tools/claim_batch.py --who opencode --note "batch of 64" addr...
    python tools/claim_batch.py --who opencode --file addresses.txt
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import take  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("addresses", nargs="*")
    ap.add_argument("--file", help="one address per line")
    ap.add_argument("--who", default="opencode")
    ap.add_argument("--note", default="batch reservation")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()

    addrs = list(a.addresses)
    if a.file:
        addrs += [ln.strip() for ln in open(a.file, encoding="utf-8")
                  if ln.strip() and not ln.startswith("#")]
    if not addrs:
        ap.error("no addresses given")

    number, state = take.fetch_ledger()
    _, db = take.unmatchable_db()
    unmatchable = {d.get("address", "").upper() for d in db}

    # one PR query for the whole batch, rather than one per address; an
    # address is 'in a PR' when its text appears in the title or body, which
    # is how take.py's own check decides it
    prs = take.open_pull_requests()
    pr_text = [f"{pr.get('title', '')}\n{pr.get('body') or ''}".lower()
               for pr in prs]

    claimed, refused = [], []
    for raw in addrs:
        addr = take.normalise(raw)
        if take.held_by(state, addr):
            refused.append((addr, "already held"))
            continue
        if addr.upper() in unmatchable:
            refused.append((addr, "recorded unmatchable"))
            continue
        if take.already_matched(addr):
            refused.append((addr, "already matched in src/"))
            continue
        a1, a2 = addr.lower(), addr[2:].lower()
        if any(a1 in text or a2 in text for text in pr_text):
            refused.append((addr, "being matched in an open PR"))
            continue
        if any(c[0] == addr for c in claimed):
            refused.append((addr, "duplicate in this batch"))
            continue
        claimed.append((addr, None))

    print(f"ledger #{number}: {len(state['rows'])} row(s) already held")
    print(f"requested {len(addrs)}, claiming {len(claimed)}, "
          f"refusing {len(refused)}")
    for addr, why in refused:
        print(f"  refused {addr}: {why}")
    if not claimed:
        return 1

    if a.dry_run:
        print("\n(dry run - nothing written)")
        for addr, _ in claimed:
            print(f"  would claim {addr}")
        return 0

    ts = take.now()
    for addr, _ in claimed:
        state["rows"].append({"address": addr, "who": a.who, "claimed_at": ts,
                              "last_seen": ts, "note": a.note,
                              "owner_id": None, "claim_id": None})
    try:
        take.write_ledger(number, state)
    except take.GhError as exc:
        print(f"write failed: {exc}")
        if exc.permission:
            print("no write access on the ledger issue - the broker request "
                  "path handles one address at a time; use reserve.py.")
        return 1

    _, check = take.fetch_ledger()
    missing = [addr for addr, _ in claimed if not take.held_by(check, addr)]
    if missing:
        print(f"LOST THE RACE for {len(missing)} address(es): {missing[:5]}")
        return 1
    take.comment(number, f"**claimed {len(claimed)} address(es)** by "
                           f"`{a.who}` - {a.note}")
    print(f"\nclaimed {len(claimed)} address(es); all confirmed held")
    return 0


if __name__ == "__main__":
    sys.exit(main())