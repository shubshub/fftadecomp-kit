#!/usr/bin/env python3
"""
status.py - how much of the ROM is actually decompiled.

    python tools/status.py                 # print the block
    python tools/status.py --write         # rewrite it into the decomp README
    python tools/status.py --verify        # recompile every src/*.c first
    python tools/status.py --check         # exit 1 if the README is stale
    python tools/status.py --badges badges # shields.io endpoint JSON

Counts two things over the functions in the code region:

    functions matched / total
    bytes matched / total        (sum of the matched functions' spans)

A function counts as matched when src/<addr>.c exists *and* its match report
says the bytes are identical.  --verify recompiles instead of trusting the
report, which is what CI should do.

--badges writes functions.json and bytes.json in the shields.io *endpoint*
format, to be published on a `badges` branch and rendered with
img.shields.io/endpoint?url=... (the same pattern dqix-decomp uses).
"""

import argparse
import json
import os
import re
import subprocess
import sys
from match_evidence import report_matches

# the status block uses block-drawing characters; Windows consoles are cp1252
for _stream in ("stdout", "stderr"):
    try:
        getattr(sys, _stream).reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass

START = "<!-- ffta-status:start -->"
END = "<!-- ffta-status:end -->"
CODE_END = 0x08150000          # end of the code region (from the analysis)

# same thresholds as the dqix-decomp badges
COLOR_THRESHOLDS = [(20, "red"), (40, "orange"), (60, "yellow"),
                    (80, "yellowgreen"), (100, "green")]


def color_for(percent):
    for threshold, color in COLOR_THRESHOLDS:
        if percent < threshold:
            return color
    return "brightgreen"


def badge(label, percent, detail=""):
    return {"schemaVersion": 1,
            "label": label,
            "message": f"{percent:.2f}%",
            "color": color_for(percent)}


def static_badge(label, percent):
    """A shields.io *static* badge URL.

    Static (rather than /endpoint?url=...) because shields.io fetches endpoint
    URLs itself and cannot read a private repository - it renders "resource not
    found".  These render for any repo, and the URL is regenerated from the
    numbers whenever the block is rewritten, so they stay current.
    """
    from urllib.parse import quote
    msg = quote(f"{percent:.2f}%", safe="")
    return (f"https://img.shields.io/badge/{quote(label, safe='')}-{msg}-"
            f"{color_for(percent)}")


def endpoint_badge(label, percent, badge_base):
    """A shields.io *endpoint* badge: self-updating, but only for a public repo.

    shields.io fetches the JSON itself, so this only works when the repository
    holding badge_base is public - and the numbers then come straight from the
    JSON on the badges branch without anyone rewriting the README.
    """
    from urllib.parse import quote
    url = f"{badge_base.rstrip('/')}/{label.split()[-1]}.json"
    return (f"https://img.shields.io/endpoint?"
            f"url={quote(url, safe='')}")


def repo_root(arg=None):
    return os.path.abspath(arg or os.environ.get("FFTA_ROOT") or os.getcwd())


def bar(frac, width=28):
    filled = int(round(frac * width))
    return "█" * filled + "░" * (width - filled)


def collect(root, verify, quiet=False):
    cfg = os.path.join(root, "config", "functions.json")
    if not os.path.exists(cfg):
        sys.exit(f"no {cfg} - run analyze first")
    fns = json.load(open(cfg, encoding="utf-8"))

    code = [f for f in fns if int(f["rom"], 16) < CODE_END]
    total_fns = len(code)
    total_bytes = sum(int(f["end"], 16) - int(f["rom"], 16) for f in code)

    src_dir = os.path.join(root, "src")
    matched_f, matched_b, problems = 0, 0, []
    for name in sorted(os.listdir(src_dir)) if os.path.isdir(src_dir) else []:
        if not name.endswith(".c"):
            continue
        addr = name[:-2].upper()
        span = next((int(f["end"], 16) - int(f["rom"], 16)
                     for f in code if f["rom"][2:].upper() == addr), None)
        if span is None:
            problems.append(f"{addr}: src/{name} does not match a known function")
            continue

        ok = False
        if verify:
            here = os.path.dirname(os.path.abspath(__file__))
            r = subprocess.run(
                [sys.executable, os.path.join(here, "match.py"),
                 "--root", root, addr, "--no-write"],
                capture_output=True, text=True)
            ok = r.returncode == 0 and "verdict MATCH - byte identical" in r.stdout.splitlines()
        else:
            rep = os.path.join(root, "docs", "match", f"{addr}.md")
            if os.path.exists(rep):
                with open(rep, encoding="utf-8") as report_file:
                    ok = report_matches(report_file.read(), root, int(addr, 16))
            else:
                problems.append(f"{addr}: no match report in docs/match/")
        if ok:
            matched_f += 1
            matched_b += span
        elif not verify:
            problems.append(f"{addr}: no current, source-bound MATCH report; re-run match.py")
        else:
            problems.append(f"{addr}: DOES NOT MATCH")

    return total_fns, matched_f, total_bytes, matched_b, problems


def badge_url(label, percent, badge_base):
    """endpoint badges when the repo is public and a badges branch exists,
    otherwise static ones (which render everywhere, but need a rewrite to
    update)"""
    if badge_base:
        return endpoint_badge(label, percent, badge_base)
    return static_badge(label, percent)


def render(total_f, matched_f, total_b, matched_b, problems, prefix="", badge_base=None):
    pf = matched_f / total_f if total_f else 0.0
    pb = matched_b / total_b if total_b else 0.0
    label = f"{prefix} " if prefix else ""
    lines = [
        START,
        "",
        "### Decompilation status",
        "",
        f"![{label}functions]({badge_url(f'{label}functions', pf * 100, badge_base)}) "
        f"![{label}bytes]({badge_url(f'{label}bytes', pb * 100, badge_base)})",
        "",
        "| Metric | Count | Percent | |",
        "|---|---|---|---|",
        f"| Functions matched | {matched_f:,} / {total_f:,} | **{pf * 100:.2f}%** | "
        f"`{bar(pf)}` |",
        f"| Bytes matched | {matched_b:,} / {total_b:,} | **{pb * 100:.2f}%** | "
        f"`{bar(pb)}` |",
        "",
        f"Measured over {total_f:,} provisional function entries in the code\n"
        f"region (`0x08000000`-`0x{CODE_END - 1:08X}`), counting indexed spans.\n"
        f"The index can contain truncated or overlapping spans; these figures\n"
        f"do not certify complete-function or whole-ROM coverage.\n"
        f"Generated by `tools/status.py` from `config/functions.json` and the\n"
        f"match reports in `docs/match/`.",
        "",
        f"**{matched_f:,} functions and {matched_b:,} bytes are byte-exact.**\n"
        f"Only exact matches are committed - see the rule in *Matching*.",
    ]
    if problems:
        lines += ["", "```", "needs attention:"] + [f"  {p}" for p in problems] + ["```"]
    lines += ["", END]
    return "\n".join(lines), pf, pb


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.environ.get("FFTA_ROOT"))
    ap.add_argument("--verify", action="store_true",
                    help="recompile every src/*.c instead of trusting the reports")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--badges", metavar="DIR",
                    help="write shields.io endpoint JSON (functions/bytes) here")
    ap.add_argument("--label-prefix", default="",
                    help="prefix each badge label, e.g. USA")
    ap.add_argument("--badge-base", default="",
                    help="raw base URL of the badges branch, e.g. "
                         "https://raw.githubusercontent.com/owner/repo/badges ; "
                         "enables self-updating endpoint badges (public repo only)")
    ap.add_argument("--static-badges", action="store_true",
                    help="always use static badge URLs, even with --badge-base")
    args = ap.parse_args()

    root = repo_root(args.root)
    tf, mf, tb, mb, problems = collect(root, args.verify)
    badge_base = None if args.static_badges else (args.badge_base or os.environ.get("FFTA_BADGE_BASE"))
    block, pf, pb = render(tf, mf, tb, mb, problems, args.label_prefix, badge_base)

    if args.badges:
        out = os.path.abspath(args.badges)
        os.makedirs(out, exist_ok=True)
        for name, pct in (("functions", pf), ("bytes", pb)):
            lbl = f"{args.label_prefix} {name}" if args.label_prefix else name
            data = badge(lbl, pct * 100)
            with open(os.path.join(out, f"{name}.json"), "w",
                      encoding="utf-8", newline="\n") as f:
                json.dump(data, f)
                f.write("\n")
            print(f"{name:<10} {data['message']:>8}  ({data['color']})")
        print(f"wrote {os.path.relpath(out, root) if out.startswith(root) else out}")

    readme = os.path.join(root, "README.md")
    current = open(readme, encoding="utf-8").read() if os.path.exists(readme) else ""

    if args.check:
        if START not in current or END not in current:
            sys.exit("README has no status markers")
        old = current[current.index(START):current.index(END) + len(END)]
        if old.strip() != block.strip():
            sys.exit("README status is stale - run: python tools/status.py --write")
        status_path = os.path.join(root, "docs", "status.md")
        if os.path.exists(status_path):
            if open(status_path, encoding="utf-8").read().strip() != block.strip():
                sys.exit("docs/status.md is stale - run: python tools/status.py --write")
        print("README status is up to date")
        return 1 if problems else 0

    if args.write:
        if START not in current:
            sys.exit(f"{readme} has no {START} / {END} markers")
        new = re.sub(re.escape(START) + r".*?" + re.escape(END), block,
                     current, flags=re.S)
        # also keep the block standalone, so CI can check the README against it
        # without needing this tool
        status_path = os.path.join(root, "docs", "status.md")
        os.makedirs(os.path.dirname(status_path), exist_ok=True)
        with open(status_path, "w", encoding="utf-8", newline="\n") as f:
            f.write(block + "\n")
        if new != current:
            with open(readme, "w", encoding="utf-8", newline="\n") as f:
                f.write(new)
            print(f"updated {os.path.relpath(readme, root)}")
        else:
            print("README status already up to date")
        print(f"wrote {os.path.relpath(status_path, root)}")
    else:
        print(block)

    if problems:
        print(f"\n{len(problems)} item(s) need attention:", file=sys.stderr)
        for p in problems:
            print(f"  {p}", file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
