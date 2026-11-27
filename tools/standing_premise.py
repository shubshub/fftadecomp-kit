"""The standing frame premise: one report line on every MATCH report whose function holds a frame.

The frame proof protects the saved registers, the saved return address and the frame words whose
contents the walk relies on, but only against the stores it can place: through SP, and through a
tracked stack alias, in the root walk and in every walked callee.  A store through any other base
is not checked (match.py's root memory-operand loop handles only alias, PC and SP bases, and
BufferCallProof._check_arguments skips every base that is not an alias), and a call or SWI is
walked only when a frame address reaches it.  Inside walked code every SP-derived value is
tracked, and an escape is refused or premised by its own line.  That a pointer from outside (an
incoming argument, a word read from memory, a result of code that is not walked, an absolute
address) never addresses the live frame, and that code the walk does not inspect (callees, the
BIOS, DMA, interrupt handlers) does not write it, is assumed, not proved: the standing premise of
the walk for every untracked pointer.  Every report that relies on it states it, in ``LINE``.

It applies exactly when the verified function holds a frame word: when code reachable from its
entry writes SP (``holds_frame``).  A frameless function has no frame word for the premise to
protect, and its report carries no line.  The test is a pure function of the function's bytes and
its mapped mode, so issuance and replay compute it alike, independently of any walk detail.

The line is carried centrally, so that no report writer can omit it:

* match.py adds it (``carry``) to the report its own writer renders, before ``--check-report``
  compares and before it writes, and to the report a selector's writer wrote, in
  ``issue_with_volatile_records``;
* match_evidence.report_matches removes it (``strip``) before any schema replay runs, after
  requiring it exactly once, verbatim, directly after the single ``* verification:`` line, iff the
  premise applies, and no such line otherwise.  The ROM it compares the report's ROM bytes with is
  match_evidence.report_rom_path's, the one every replay reads;
* issued_report_pins, which status.py calls only once ``--check-report`` has found the saved report
  identical to the one match.py writes now (so that the line is already bound), and
  saved_selectors, which only parses, use ``without``.

Every schema replay therefore sees exactly the text it saw before this line existed.  The line is
bound by recomputation and whole-text comparison (``--check-report`` for match.py's own reports,
``strip`` for every replay), as the callee-saved premise lines are; it is in no proof digest.

A rule that relies on the premise beyond the frame proof (keeping a fact across stores the walk
cannot place) calls ``require`` and names ``POLICY`` in its own fingerprinted evidence; it never
restates the premise in its own words.

The reachability test (``holds_frame``) decodes from the entry with capstone and follows the
fallthrough, B and Bcc targets inside the span, BL inside the span on both edges (a local long
branch) and BL outside the span or SWI to the fallthrough.  An agbcc far jump (far_jump_profile)
is a BL inside the span whose only successor is its target; following its fall-through as well
only adds paths, so the test needs no far-jump decision and stays a function of the bytes alone.  BX through LR or a low register and B
outside the span end a path.  It is True when a reached instruction writes SP (a push, a pop, an
SP adjustment, an SP-writeback transfer, a move to SP), and conservatively True when it reaches a
halfword it cannot decode or that is not an ARMv4T Thumb encoding (armv4t.instruction; Capstone
also decodes Thumb-2), runs off the span, reaches a transfer it does not follow (MOV, ADD or LDR to
PC, BX PC, BLX, an LDM loading PC, any other jump) or when the mapping gives no unique mode for the
address.  It never imports match, so match.py's ``__main__`` copy is irrelevant to it.
"""
import json
import re
from pathlib import Path

from capstone import CS_ARCH_ARM, CS_GRP_INT as ARM_GRP_INT, CS_GRP_JUMP as ARM_GRP_JUMP, CS_MODE_ARM, \
    CS_MODE_THUMB, Cs, CsError
from capstone.arm import (ARM_CC_AL, ARM_CC_INVALID, ARM_INS_B, ARM_INS_BL, ARM_INS_BLX, ARM_INS_BX,
                          ARM_OP_IMM, ARM_OP_REG, ARM_REG_PC, ARM_REG_SP)

import armv4t

POLICY = "untracked-pointer-frame-v1"
PREFIX = "* frame premise: "
LINE = (f"{PREFIX}`{POLICY}`; unproved premise: no pointer the walk does not derive from SP (an incoming "
        "argument, a word read from memory, a result of code the walk does not inspect, or an absolute "
        "address) addresses stack that this function or a callee the walk inspects has allocated, except an "
        "escaped address used only as an escape premise of this report states; and no code the walk does not "
        "inspect (a callee, the BIOS, DMA or an interrupt handler) writes that stack other than the stack "
        "arguments it is passed, except as a summary or premise line of this report states")
ANCHOR = "* verification: "
ROM_BASE = 0x08000000
ROM_BYTES = re.compile(r"\* ROM bytes: `((?:[0-9a-f]{2})+)` \(([1-9][0-9]*) bytes\)")
# Any bullet naming the premise, however spaced or marked: only LINE, in its one place, is admitted.
LIKE = re.compile(r"\s*[*+-]\s*frame\s+premise", re.IGNORECASE)
MAX_STEPS = 1 << 16

_ENGINES = {}


def _engine(thumb):
    engine = _ENGINES.get(thumb)
    if engine is None:
        engine = _ENGINES[thumb] = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
        engine.detail = True
    return engine


def holds_frame(data, address, thumb):
    """Whether code reachable from the entry of `data` (at `address`) writes SP, or cannot be followed."""
    data = bytes(data)
    end = address + len(data)
    if not data or address % (2 if thumb else 4):
        return True
    engine = _engine(thumb)
    seen = set()
    pending = [address]
    steps = 0
    while pending:
        pc = pending.pop()
        if pc in seen:
            continue
        if not address <= pc < end:
            return True                      # control runs off the span
        seen.add(pc)
        steps += 1
        if steps > MAX_STEPS:
            return True
        offset = pc - address
        decoded = list(engine.disasm(data[offset:offset + 4], pc, 1))
        if not decoded or pc + decoded[0].size > end:
            return True                      # an undecodable halfword, or an instruction past the span
        instruction = decoded[0]
        swi = thumb and instruction.size == 2 and bytes(instruction.bytes)[1] == 0xDF
        if thumb and not swi and not armv4t.instruction(instruction):
            return True                      # not an ARMv4T Thumb encoding: Capstone also decodes Thumb-2
        try:
            _, written = instruction.regs_access()
        except CsError:
            return True
        if ARM_REG_SP in written:
            return True
        if swi:
            pending.append(pc + 2)           # SWI returns to the next instruction
            continue
        following = pc + instruction.size
        conditional = instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID)
        operands = instruction.operands
        if instruction.id == ARM_INS_B:
            if len(operands) != 1 or operands[0].type != ARM_OP_IMM:
                return True
            target = operands[0].imm
            if address <= target < end:
                pending.append(target)
            if conditional:
                pending.append(following)
            continue
        if instruction.id == ARM_INS_BL:
            if len(operands) != 1 or operands[0].type != ARM_OP_IMM:
                return True
            target = operands[0].imm
            if address <= target < end:
                pending.append(target)       # a local long branch: both edges
            pending.append(following)
            continue
        if instruction.id == ARM_INS_BX:
            if len(operands) != 1 or operands[0].type != ARM_OP_REG or operands[0].reg == ARM_REG_PC:
                return True
            if conditional:
                pending.append(following)
            continue                         # a return, or a transfer out of the function
        if instruction.id == ARM_INS_BLX or ARM_REG_PC in written or ARM_GRP_JUMP in instruction.groups:
            return True                      # a transfer this test does not follow
        if not thumb and ARM_GRP_INT in instruction.groups:
            pending.append(following)        # SWI returns to the next instruction
            continue
        pending.append(following)
    return False


def _mode(root, address):
    """'thumb' or 'arm' from the unique config/functions.json entry at `address`, else None."""
    try:
        entries = json.loads((Path(root) / "config" / "functions.json").read_text(encoding="utf-8"))
    except (OSError, ValueError, UnicodeError):
        return None
    if not isinstance(entries, list):
        return None
    modes = []
    for entry in entries:
        try:
            if isinstance(entry, dict) and int(entry["rom"], 16) == address:
                modes.append(entry.get("mode"))
        except (KeyError, TypeError, ValueError):
            continue
    return modes[0] if len(modes) == 1 and modes[0] in ("thumb", "arm") else None


def _function_bytes(lines, root, address):
    """The report's single `* ROM bytes:` value, required to equal the ROM at `address`."""
    records = [line for line in lines if line.lstrip().startswith("* ROM bytes")]
    found = ROM_BYTES.fullmatch(records[0]) if len(records) == 1 else None
    if found is None:
        raise ValueError("frame premise: report has no single canonical ROM bytes line")
    data = bytes.fromhex(found[1])
    if len(data) != int(found[2]) or address < ROM_BASE:
        raise ValueError("frame premise: report ROM bytes line is inconsistent")
    import match_evidence          # the ROM every replay reads, as the replays read it
    rom = Path(match_evidence.report_rom_path(root)).read_bytes()
    if rom[address - ROM_BASE:address - ROM_BASE + len(data)] != data:
        raise ValueError("frame premise: report ROM bytes differ from the ROM")
    return data


def applies(data, root, address):
    """Whether the premise applies to the function `data` at `address`: its mapped mode, and holds_frame."""
    mode = _mode(root, address)
    return mode is None or holds_frame(data, address, mode == "thumb")


def _anchor(lines):
    anchors = [index for index, line in enumerate(lines) if line.startswith(ANCHOR)]
    if len(anchors) != 1:
        raise ValueError("frame premise: report has no single verification line")
    return anchors[0]


def carry(report, root, address):
    """`report` with LINE directly after its verification line iff the premise applies."""
    lines = report.split("\n")
    if any(LIKE.match(line) for line in lines):
        raise ValueError("frame premise: report already carries a frame premise line")
    anchor = _anchor(lines)
    if applies(_function_bytes(lines, root, address), root, address):
        lines.insert(anchor + 1, LINE)
    return "\n".join(lines)


def strip(report, root, address):
    """`report` without LINE, once it is there exactly when and where it must be; ValueError otherwise."""
    lines = report.split("\n")
    anchor = _anchor(lines)
    present = [index for index, line in enumerate(lines) if LIKE.match(line)]
    if applies(_function_bytes(lines, root, address), root, address):
        if present != [anchor + 1] or lines[anchor + 1] != LINE:
            raise ValueError("frame premise: the premise line is missing, altered, misplaced or repeated")
        del lines[anchor + 1]
    elif present:
        raise ValueError("frame premise: a frameless function's report carries the premise line")
    return "\n".join(lines)


def without(report):
    """`report` without any line exactly equal to LINE, for readers that only parse; no check."""
    return "\n".join(line for line in report.split("\n") if line != LINE)


def require(data, address, thumb):
    """Raise unless the premise applies to `data` at `address`, for a rule that relies on it."""
    if not holds_frame(data, address, thumb):
        raise ValueError(f"rule relies on `{POLICY}`, which a frameless function's report does not state")
