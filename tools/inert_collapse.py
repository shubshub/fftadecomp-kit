"""The collapse compile of a justified inert-control-flow test (kit#201).

`if (c) X; else X;` is admitted only where the ROM keeps the test's own
instructions or its frame effect (the maintainer's ruling: "ship if the ROM
keeps the test").  A comment cannot show that, so match.py compiles the
addressed translation unit again with the test collapsed to `X;` and compares
the two.  This module finds the test in the preprocessed text, collapses it and
classifies what the original keeps that the collapsed form does not:

* the same bytes: the test leaves nothing in the ROM, and is refused;
* otherwise the two listings are counted per mnemonic, operands ignored: the
  original must have more loads (`ldr`, `ldrh`, `ldrb`, `ldrsh`, `ldrsb`, not
  counting `ldr rN, .Ln` literal-pool loads or loads based on sp, which are
  spill reloads and stack arguments), more compares or tests (`cmp`,
  `cmn`, `tst`, `and`), or a frame only the test explains (frame: the
  collapsed listing pushes no lr, and the original's frame saves lr alone or
  serves a call the collapsed listing lacks).
  Operands carry register numbers, stack offsets and label numbers, which move
  with the allocation, so they never count.  A difference in register
  allocation alone is refused.

The record names the test, what it keeps, and every instruction that differs,
so a reviewer can tell a test or frame trace from one that only moves registers.
"""
import collections
import re

import plausible

RECORD = "* inert test trace: "
MARKER = re.compile(r'^# (\d+) "((?:\\.|[^"\\])*)"', re.M)
# a condition that writes something cannot be dropped with the test: ++, --, = and every compound assignment
# (the last alternative catches the `=` of `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=` and `^=` too, but not of the
# shifts, whose `=` follows `<` or `>`)
SIDE_EFFECT = re.compile(r"\+\+|--|<<=|>>=|(?<![=!<>])=(?!=)")
LABEL_NUMBER = re.compile(r"\.L\d+\b")
POOL_LOAD = re.compile(r"^ldr\s+\S+\s*,\s*(?:\.L\w*|=)")
# a load from the frame: a spill reload or a stack argument, which register pressure moves
STACK_LOAD = re.compile(r"^ldr\w*\s+\w+\s*,\s*\[sp\b")
# a call: a bl to a symbol (a bl to a local label is a far branch, not a call)
CALL = re.compile(r"^bl\s+(?!\.L)\S")
LR_PUSH = re.compile(r"^push\s*\{[^}]*\blr\b")
LONE_LR_PUSH = re.compile(r"^push\s*\{\s*lr\s*\}$")
REGISTER = re.compile(r"\b(?:r(?:1[0-2]|[0-9])|sl|fp|ip|sb)\b")
LOADS = ("ldr", "ldrh", "ldrb", "ldrsh", "ldrsb")
TESTS = ("cmp", "cmn", "tst", "and")


class TraceError(ValueError):
    """the test leaves no trace the ruling counts, or cannot be collapsed"""


def source_lines(preprocessed):
    """(file, line) of each line of cpp's output, from its line markers (None before the first)"""
    out, current = [], None
    for text in preprocessed.split("\n"):
        marker = MARKER.match(text)
        if marker:
            current = (marker.group(2), int(marker.group(1)) - 1)
            out.append(None)
            continue
        if current is not None:
            current = (current[0], current[1] + 1)
        out.append(current)
    return out


def located(preprocessed, file, line):
    """the one inert match in the preprocessed text whose `if` comes from line `line` of `file`"""
    code = plausible.strip_comments_and_strings(preprocessed)
    lines = source_lines(preprocessed)
    found = [match for match in plausible.inert_matches(code)
             if lines[preprocessed.count("\n", 0, match.start())] == (file, line)]
    if len(found) != 1:
        raise TraceError(f"the inert test at {file} line {line} is not one test in the preprocessed source")
    return found[0]


def collapse(preprocessed, file, line):
    """the preprocessed text with that test replaced by its arm: `if (c) X; else X;` -> `X;` (lines kept)"""
    match = located(preprocessed, file, line)
    if SIDE_EFFECT.search(match.group("cond")):
        raise TraceError(f"the inert test at {file} line {line} has a condition with a side effect")
    span = preprocessed[match.start():match.end()]
    arm = preprocessed[match.start("a"):match.end("a")].strip()
    return preprocessed[:match.start()] + arm + ";" + "\n" * span.count("\n") + preprocessed[match.end():]


def instructions(assembly):
    """the instruction lines of an agbcc listing: no labels, directives or comments"""
    out = []
    for text in assembly.split("\n"):
        text = text.split("@", 1)[0].strip()
        if not text or text.startswith(".") or text.endswith(":"):
            continue
        out.append(" ".join(text.split()))
    return out


def functions(assembly):
    """{label: its instruction lines} of each function of an agbcc listing, split at labels that are not local
    (`.L`) labels"""
    out, current = {}, None
    for text in assembly.split("\n"):
        text = text.split("@", 1)[0].strip()
        if text.endswith(":") and not text.startswith("."):
            current = out.setdefault(text[:-1], [])
        elif text and not text.startswith(".") and not text.endswith(":") and current is not None:
            current.append(" ".join(text.split()))
    return out


def normalised(instruction):
    """the instruction without its register numbers and push/pop widths, or None for a register-to-register move"""
    mnemonic, _, operands = instruction.partition(" ")
    parts = [part.strip() for part in operands.split(",")]
    if mnemonic == "mov" and len(parts) == 2 and all(REGISTER.fullmatch(part) for part in parts):
        return None
    if mnemonic == "add" and len(parts) == 3 and REGISTER.fullmatch(parts[0]) and \
            REGISTER.fullmatch(parts[1]) and parts[2] == "#0":
        return None
    if mnemonic in ("push", "pop"):
        kept = [name for name in ("lr", "pc") if re.search(r"\b" + name + r"\b", operands)]
        return f"{mnemonic} {{{', '.join(kept)}}}"
    return f"{mnemonic} {LABEL_NUMBER.sub('.L', REGISTER.sub('r', operands))}".strip()


def counts(listing):
    """(loads, tests) of a listing; literal-pool loads are not loads of anything the source reads, and loads
    based on sp are spill reloads and stack arguments, which move with the allocation"""
    loads = sum(1 for instruction in listing
                if instruction.split(" ")[0] in LOADS and not POOL_LOAD.match(instruction)
                and not STACK_LOAD.match(instruction))
    tests = sum(1 for instruction in listing if instruction.split(" ")[0] in TESTS)
    return loads, tests


def frame(original, collapsed):
    """does a function of the original listing keep a frame that only the test explains (framed, per function)?

    The collapsed listing must push no lr at all (a frameless leaf), and the original's frame must either
    save lr alone or serve a call the collapsed listing lacks.  agbcc gives a leaf whose test branch it
    later removes a lone `push {lr}` (every probe of a frameless leaf shows it: the frame is laid out while
    the branch exists), and a call in the condition needs a frame of its own.  A frame that also saves
    callee-saved registers can come from the register pressure of keeping the condition live, so on its
    own it never counts; nor does any frame difference when both listings have one."""
    mine, theirs = functions(original), functions(collapsed)
    return any(framed(mine[name], theirs[name]) for name in mine.keys() & theirs.keys())


def framed(original, collapsed):
    """frame() for one function's instructions in each listing"""
    pushes = [instruction for instruction in original if LR_PUSH.match(instruction)]
    if not pushes or any(LR_PUSH.match(instruction) for instruction in collapsed):
        return False
    calls = lambda listing: sum(1 for instruction in listing if CALL.match(instruction))
    return any(LONE_LR_PUSH.match(instruction) for instruction in pushes) or calls(original) > calls(collapsed)


def trace(original, collapsed):
    """(kinds, extra, missing): what the original listing keeps that the collapsed one does not.

    kinds compares per-mnemonic counts, operands ignored: load (more loads that
    are neither literal-pool nor sp-based), test (more cmp, cmn, tst or and) and
    frame (see frame()).
    extra and missing are the instructions whose normalised forms the other
    listing lacks, in listing order and with label numbers dropped, for the
    record: they show the reviewer what differs, and never decide."""
    def counted(listing):
        return collections.Counter(form for form in map(normalised, listing) if form is not None)

    first, second = instructions(original), instructions(collapsed)
    over, under = counted(first) - counted(second), counted(second) - counted(first)

    def pick(listing, surplus):
        surplus, out = collections.Counter(surplus), []
        for instruction in listing:
            form = normalised(instruction)
            if form is not None and surplus[form] > 0:
                surplus[form] -= 1
                out.append(LABEL_NUMBER.sub(".L", instruction))
        return out

    extra, missing = pick(first, over), pick(second, under)
    kinds = [kind for kind, mine, theirs in zip(("load", "test"), counts(first), counts(second)) if mine > theirs]
    if frame(original, collapsed):
        kinds.append("frame")
    return kinds, extra, missing


def record(file, line, kinds, extra, missing, size, collapsed_size):
    """the report line for one test whose trace counts"""
    return (f"{RECORD}`{file}` line {line} keeps {' and '.join(kinds)}: "
            f"{size} bytes against {collapsed_size} with the arms collapsed; "
            f"only in the original: {'; '.join(extra) or 'none'}; only collapsed: {'; '.join(missing) or 'none'}")
