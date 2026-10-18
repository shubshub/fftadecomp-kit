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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--strict", action="store_true",
                    help="treat suspect findings as errors too (default: "
                         "suspect findings also fail unless justified)")
    args = ap.parse_args()

    total = 0
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
            print(f"{f}:")
            for line, rid, sev, msg in findings:
                print(f"  {os.path.basename(f)}:{line}: {sev.upper()}: {rid}")
                print(f"      {msg}")
    if total and not args.quiet:
        print(f"\n{total} finding(s): the code does not look like something a "
              f"developer would have written", file=sys.stderr)
        print("A byte-identical compile is not a match if the source is "
              "implausible.", file=sys.stderr)
    return 1 if total else 0


if __name__ == "__main__":
    sys.exit(main())