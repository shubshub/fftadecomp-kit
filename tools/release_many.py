"""Release several reservations in one ledger write.

take.py releases one address at a time, and each release is a read of the ledger
issue, an edit of its body, and a re-read to confirm.  Clearing a batch of
sixty-four that way is a hundred and ninety round trips, and every one is a
chance for somebody else's claim to land in between.

This does it in one pass: read the ledger, drop the rows that are ours and
were asked for, write the body once, and re-read to confirm they are gone.
Rows held by anyone else are never touched, and a row that is not ours is
reported rather than removed.

    python tools/release_many.py --who opencode            # all of ours
    python tools/release_many.py 0x08011058 0x08011040      # specific rows
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import take  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("addresses", nargs="*")
    ap.add_argument("--who", default=None,
                    help="release every row held by this lane")
    ap.add_argument("--reason", default="batch released")
    a = ap.parse_args()

    number, state = take.fetch_ledger()
    rows = state["rows"]

    if a.addresses:
        wanted = {take.normalise(x).upper() for x in a.addresses}
        drop = [r for r in rows
                if str(r.get("address", "")).upper() in wanted]
        kept_note = "not held"
    elif a.who:
        drop = [r for r in rows if r.get("who") == a.who]
        kept_note = f"held by another lane"
    else:
        ap.error("give addresses or --who")

    if not drop:
        print("nothing to release")
        return 0

    state["rows"] = [r for r in rows if r not in drop]
    try:
        take.write_ledger(number, state)
    except take.GhError as exc:
        print(f"write failed: {exc}")
        return 1

    _, check = take.fetch_ledger()
    still = [str(r.get("address")) for r in check["rows"]
             if r in drop]
    if still:
        print(f"FAILED to release {len(still)}: {still[:5]}")
        return 1
    print(f"released {len(drop)} reservation(s)")
    for r in drop:
        print(f"  {r.get('address')}  ({r.get('who')})")
    return 0


if __name__ == "__main__":
    sys.exit(main())