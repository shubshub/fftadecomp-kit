#!/usr/bin/env python3
"""
plausible.py - reject decompiled C that only exists to make bytes match.

A matching decomp is supposed to reconstruct the source a developer actually
wrote.  Byte-matching by trickery is worthless: inline asm, pragma surgery and
padding that exists purely to steer the compiler all produce a "match" that
proves nothing and cannot be maintained.

So every function is also checked for implausibility.  Anything that trips a
rule is IMPLAUSIBLE and does not count as a match, however well the bytes line
up.

    python tools/plausible.py src/08017514.c        # check files
    python tools/plausible.py --quiet src/          # just the exit status

Rules
------
error   the construct has no plausible reading as original source
suspect the construct is legitimate *somewhere*, but must be justified here

A finding is cleared by a comment containing `plausible:` on the same line or
the line above, e.g. a genuine I/O register access:

    /* plausible: hardware register, volatile is required here */
    *(volatile u16 *)0x04000000 = v;
"""

import argparse
import json
import os
import re
import sys

JUSTIFY = "plausible:"

# id, severity, pattern, message
RULES = [
    # --- constructs that are a codegen hack by definition
    ("inline-asm", "error", r"__asm__|\basm\s*(?:__volatile__|volatile|goto|inline)?\s*\(",
     "inline assembly: the point of a matching decomp is C that compiles to the "
     "original code, not asm pasted into a C file"),
    ("asm-include", "error", r'#\s*include\s+"[^"]*\.(s|S)"',
     "including an assembly file"),
    ("optimize-pragma", "error", r"#\s*pragma\s+(?:GCC\s+)?optimize|__attribute__\s*\(\(\s*optimize",
     "optimisation pragma/attribute: changes code generation outside the source"),
    ("no-standard-errors", "error", r"#\s*pragma\s+GCC\s+diagnostic",
     "disabling diagnostics to silence warnings the original would not have"),
    ("dead-code", "error", r"\bif\s*\(\s*0\s*\)|\bwhile\s*\(\s*0\s*\)|#\s*if\s+0\b",
     "dead code whose only purpose is to steer the compiler"),
    ("empty-body", "error", r"\)\s*\{\s*\}",
     "empty function body"),
    ("placeholder", "error", r"\?\?\?|\bTODO\b|\bFIXME\b|\bUNIMPLEMENTED\b|not implemented",
     "placeholder body"),
    ("volatile", "error", r"\bvolatile\b",
     "volatile: it suppresses reordering, which is the classic way to force a "
     "byte match (real I/O code is the only legitimate use - justify it)"),
    ("attribute-steering", "error",
     r"__attribute__\s*\(\(\s*(used|section|alias|weak|naked|constructor|destructor)",
     "attribute that only affects code placement or emission"),

    # --- legitimate somewhere, must be justified here
    ("noinline", "suspect", r"\bnoinline\b|\balways_inline\b",
     "inlining attribute: fine in real code, but it is also a way to force a "
     "codegen difference"),
    ("pragma-pack", "suspect", r"#\s*pragma\s+pack",
     "struct packing: changes field offsets, which can be legitimate - say why"),
    ("pad-named", "suspect", r"\b(?:pad|padding|_pad)\s*\[",
     "padding named 'pad': if the real members are unknown, name them "
     "'unknown' and say so, rather than leaving steering padding"),
    ("rom-address", "suspect", r"0x0[89][0-9A-Fa-f]{6}\b(?![^;]*\))",
     "an address inside ROM used as a value: ROM is not writable, so this is "
     "usually a hack rather than a pointer"),
    ("hack-vocabulary", "suspect", r"\bhack\b|\bworkaround\b|force the compiler|"
     r"so the compiler will|to make (?:it|the) (?:match|compile)|codegen hack",
     "the comment admits the source exists to steer the compiler"),
]


def strip_comments_and_strings(text):
    """replace comments and string/char literals with spaces, keeping offsets"""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            while i < n and not (text[i] == "*" and i + 1 < n and text[i + 1] == "/"):
                out[i] = " "
                i += 1
            for k in range(i, min(i + 2, n)):
                out[k] = " "
            i += 2
        elif c in "\"'":
            q = c
            out[i] = " "
            i += 1
            while i < n and text[i] != q:
                if text[i] == "\\":
                    out[i] = " "
                    if i + 1 < n:
                        out[i + 1] = " "
                    i += 2
                    continue
                out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
        else:
            i += 1
    return "".join(out)


def justified(text, line_no):
    """True if a comment containing `plausible:` covers this line"""
    lines = text.split("\n")
    for idx in (line_no - 1, line_no - 2):
        if 0 <= idx < len(lines) and JUSTIFY in lines[idx]:
            return True
    return False


def inert_control_flow(text):
    """find `if (c) X; else X;` - identical arms, so the test means nothing.

    This is the shape that appeared in a rejected match: the branches store the
    same value, so the only effect is to make the compiler keep a frame it
    would otherwise drop.  Semantically it is `X;`, and nobody writes that.
    """
    hits = []
    pat = re.compile(
        r"\bif\s*\((?P<cond>[^()]*)\)(?P<a>[^;{}]*?)\s*;?\s*else"
        r"\s*(?P<b>[^;{}]*?)\s*;")
    for m in pat.finditer(text):
        a = " ".join(m.group("a").split())
        b = " ".join(m.group("b").split())
        if a and a == b:
            line = text.count("\n", 0, m.start()) + 1
            hits.append((line, "inert-control-flow", "suspect",
                         f"`if ({m.group('cond').strip()}) {a}; else {b};` - both "
                         f"arms do the same thing, so the test exists only to "
                         f"change the generated code"))
    return hits


def check_text(text, origin=""):
    """returns list of findings: (line, rule, severity, message)"""
    code = strip_comments_and_strings(text)
    findings = []
    for rid, sev, pat, msg in RULES:
        for m in re.finditer(pat, code):
            line = code.count("\n", 0, m.start()) + 1
            if sev == "suspect" and justified(text, line):
                continue
            # an inline-asm-looking thing inside a comment is not code
            findings.append((line, rid, sev, msg))
    findings += inert_control_flow(code)
    # comments are where hackiness gets admitted, so scan them raw too
    for i, raw in enumerate(text.split("\n"), 1):
        if JUSTIFY in raw:
            continue
        for rid, sev, pat, msg in RULES:
            if rid == "hack-vocabulary" and re.search(pat, raw):
                findings.append((i, rid, sev, msg))
    findings.sort(key=lambda f: (f[0], f[1]))
    return findings


def check_file(path):
    try:
        text = open(path, encoding="utf-8", errors="replace").read()
    except OSError as e:
        return [(0, "unreadable", "error", str(e))]
    return check_text(text, os.path.basename(path))


def asm_allow_path():
    return os.environ.get("FFTA_ASM_ALLOW") or os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "asm_allow.json")


def asm_allowed(addr):
    """is this address on the maintainer's hand-asm allow list?

    The list exists so that a function which provably cannot come from
    plausible C can still be solved, by hand-written assembly, *by decision*
    rather than by an agent quietly hacking its way to a match.  Only the
    repository maintainer may add entries; nothing here writes the file.
    """
    path = asm_allow_path()
    if not addr:
        return None
    try:
        doc = json.load(open(path, encoding="utf-8"))
    except (OSError, ValueError):
        return None
    for entry in doc.get("entries", []):
        if str(entry.get("address", "")).upper() == str(addr).upper():
            return entry
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--strict", action="store_true",
                    help="treat suspect findings as errors too (default: "
                         "suspect findings also fail unless justified)")
    ap.add_argument("--addr", default=None,
                    help="the ROM address these sources implement, so the "
                         "hand-asm allow list can be consulted")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    total = 0
    all_findings = []
    for p in args.paths:
        files = sorted(
            os.path.join(p, f) for f in os.listdir(p)
            if f.endswith(".c") or f.endswith(".h")) \
            if os.path.isdir(p) else [p]
        for f in files:
            findings = check_file(f)
            if not findings:
                continue
            total += len(findings)
            all_findings.extend(
                {"file": f, "line": l, "rule": r, "severity": s, "message": m}
                for l, r, s, m in findings)
            if not args.json:
                print(f"{f}:")
                for line, rid, sev, msg in findings:
                    print(f"  {os.path.basename(f)}:{line}: {sev.upper()}: {rid}")
                    print(f"      {msg}")

    allowed = asm_allowed(args.addr) if total else None
    if args.json:
        print(json.dumps({"findings": all_findings, "total": total,
                          "addr": args.addr,
                          "hand_asm_allowed": bool(allowed),
                          "allow_entry": allowed}, indent=2))
        return 1 if total else 0

    if total:
        print(f"\n{total} finding(s): the code does not look like something a "
              f"developer would have written", file=sys.stderr)
        print("A byte-identical compile is not a match if the source is "
              "implausible.", file=sys.stderr)
        if args.addr:
            if allowed:
                print(f"\n{args.addr} IS on the hand-asm allow list "
                      f"({allowed.get('reason', 'no reason recorded')}).",
                      file=sys.stderr)
                print("A match here is HAND-ASM, not a decompilation.",
                      file=sys.stderr)
            else:
                print(f"\n{args.addr} is NOT on the hand-asm allow list, so a "
                      f"match that needs hand asm is not acceptable here.",
                      file=sys.stderr)
                print("Park it and say so; only the maintainer may add an "
                      "entry to tools/asm_allow.json.", file=sys.stderr)
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())