"""The exact field lines of a plain-schema match report (kit #247).

`match.py` writes a fixed list of `* name: value` lines for each plain schema
(the leaf, frame, call, data and plain buffer-call schemas). Replay used to look
for the lines it needs and ignore everything else, so a saved report could carry
fields of other profiles, or a second, different copy of a bound field. `check`
admits exactly the lines the writer produces for the claimed schema:

1. every field line uses a prefix the writer emits for that schema. A field
   line is any bullet: a line whose first non-blank character (Unicode blanks
   included) is `*`, `-` or `+` followed by a blank, so only the writer's own
   `* name: ` form at the start of the line can match. A plausible report has
   no findings list, so the writer emits no other bullet;
2. each field appears exactly once; the two self-call lines appear together or
   not at all. On the buffer schemas, the other `* buffer ` lines (loop replay,
   BIOS, copy-helper and switch-callee summary lines) may repeat:
   `match_evidence.buffer_report_matches` requires them to equal the
   recomputed proof lines exactly and in order. On the three framed schemas
   without buffer calls, the `* DMA fill` lines may repeat:
   `dma_fill_profile.check_report` requires them to equal the recomputed
   block exactly, right after the stack-frame line;
3. `* source:` names the file match.py compiles for the address (`source_path`:
   `src/<ADDR>.c`, else the first `<ADDR>.c` under `src/` in sorted order), and
   `* hand-asm allow list:` is `not listed` or `listed (...)`. The source
   fingerprint already binds that path, so a module move needs regeneration
   either way; this line must then name the new folder;
4. the field lines appear in the writer's order (`ORDER`), all before the
   `**MATCH` verdict line.

Values replay recomputes (fingerprints, summaries, bytes) keep their checks in
`match_evidence`. Allowlisted volatile records are stripped before this check.
Library-unit lines are admitted at most once each; `library_units` validates them.

`check_labels` holds the claimed labels to the walk replay already runs, as
`match.py` derives them:

5. a frame schema iff the reached Thumb code uses the stack frame;
6. a call schema, or the call summary on a data schema, iff a reached BL leaves
   the function or re-enters its entry (self calls are calls);
7. a data schema only if a data relocation could exist: a reached
   PC-relative `ldr` loads a word inside the function whose value lies outside
   it (`data_literal`). The converse cannot be checked from the bytes: a
   literal outside the function may be a raw constant.
"""
import os
from pathlib import Path
import re

from dma_fill_profile import MARKER as DMA_FILL_LINES  # its summary, premise and manifest lines

# Every bullet is a field line: the first non-blank character (Unicode blanks included) is `*`, `-`
# or `+`, followed by a blank.
FIELD = re.compile(r"\s*[*+-]\s")

COMMON = ("* source: ", "* verification: ", "* source SHA-256: ", "* compiler: ",
          "* verified extent: ", "* relocations: ", "* ROM bytes: ", "* compiled : ",
          "* source plausibility: ", "* hand-asm allow list: ")
FRAME = ("* stack frame: ",)
CALLS = ("* mapping SHA-256: ", "* control flow: ")
DATA = ("* data symbols SHA-256: ",)
BUFFER = ("* buffer calls: ", "* buffer proof SHA-256: ")
PROOF_LINES = "* buffer "
SELF_CALLS = ("* self calls: ", "* self call sites: ")
UNIT = ("* library unit: ", "* unit toolchain: ", "* unit compiler SHA-256: ", "* unit orphan constants: ")

HAND_ASM = re.compile(r"not listed|listed \(.*\)")

# The writer's field order (match.py's report writer); the buffer proof lines follow their fingerprint.
ORDER = (COMMON[:3] + FRAME + (DMA_FILL_LINES,) + BUFFER + (PROOF_LINES,) + CALLS + SELF_CALLS + DATA + UNIT + COMMON[3:])


def layout(schema):
    """(required, optional, repeated prefixes) for a plain schema, or None for any other."""
    import match_evidence as evidence
    shapes = {  # schema: (framed, calls, data, buffer)
        evidence.SCHEMA: (False, False, False, False),
        evidence.FRAMED_SCHEMA: (True, False, False, False),
        evidence.LINKED_SCHEMA: (False, True, False, False),
        evidence.FRAMED_LINKED_SCHEMA: (True, True, False, False),
        evidence.DATA_SCHEMA: (False, True, True, False),
        evidence.FRAMED_DATA_SCHEMA: (True, True, True, False),
        evidence.BUFFER_SCHEMA: (True, True, False, True),
        evidence.STACK_BUFFER_SCHEMA: (True, True, False, True),
    }
    if schema not in shapes:
        return None
    framed, calls, data, buffer = shapes[schema]
    required = COMMON + (FRAME if framed else ()) + (CALLS if calls else ()) + \
        (DATA if data else ()) + (BUFFER if buffer else ())
    optional = UNIT + (SELF_CALLS if calls and not buffer else ())
    return required, optional, ((PROOF_LINES,) if buffer else ()) + ((DMA_FILL_LINES,) if framed and not buffer else ())


def source_path(root, address):
    """The source match.py compiles and names in `* source:`, relative to root; None if there is none."""
    candidates = [Path(root, "src", f"{address:08X}.c")] + sorted(Path(root, "src").rglob(f"{address:08X}.c"))
    found = next((candidate for candidate in candidates if os.path.exists(candidate)), None)
    return None if found is None else os.path.relpath(found, root).replace(os.sep, "/")


def check(lines, schema, address, root):
    """Raise ValueError unless the field lines are exactly those `match.py` writes for `schema`."""
    shape = layout(schema)
    if shape is None:
        raise ValueError(f"not a plain report schema: {schema}")
    required, optional, repeated = shape
    allowed = required + optional
    counts = dict.fromkeys(allowed, 0)
    slots = []
    for index, line in enumerate(lines):
        if not FIELD.match(line):
            continue
        prefix = next((prefix for prefix in allowed if line.startswith(prefix)), None)
        if prefix is None:
            prefix = next((prefix for prefix in repeated if line.startswith(prefix)), None)
        if prefix is None:
            raise ValueError(f"plain report field is not written for this schema: {line[:60]}")
        if prefix in counts:
            counts[prefix] += 1
        slots.append((index, ORDER.index(prefix)))
    for prefix, count in counts.items():
        if count > 1:
            raise ValueError(f"plain report field is duplicated: {prefix.strip()}")
        if count == 0 and prefix in required:
            raise ValueError(f"plain report field is missing: {prefix.strip()}")
    if counts.get(SELF_CALLS[0], 0) != counts.get(SELF_CALLS[1], 0):
        raise ValueError("plain report self-call lines are incomplete")
    # Each prefix but the repeated lines' occurs once, so a non-decreasing slot sequence is the writer's order.
    if [slot for _, slot in slots] != sorted(slot for _, slot in slots):
        raise ValueError("plain report fields are not in the writer's order")
    verdict = next((index for index, line in enumerate(lines) if line.startswith("**")), len(lines))
    if any(index > verdict for index, _ in slots):
        raise ValueError("plain report field follows the verdict")
    value = {prefix: line[len(prefix):] for line in lines for prefix in ("* source: ", "* hand-asm allow list: ")
             if line.startswith(prefix)}
    source = source_path(root, address)
    if source is None or value["* source: "] != f"`{source}`":
        raise ValueError("plain report source line does not name the source match.py compiles")
    if HAND_ASM.fullmatch(value["* hand-asm allow list: "]) is None:
        raise ValueError("plain report hand-asm line has no writer form")


def data_literal(reached, address, data):
    """Whether a reached PC-relative `ldr` loads a word of `data` whose value lies outside the function.

    match.py binds a data symbol only through an R_ARM_ABS32 relocation on a complete aligned word inside
    the function whose linked value lies outside it (`link_calls`), and agbcc writes such a word only into
    a literal pool. Thumb code reads a pool word only with `ldr rd, [pc, #imm]`, the one PC-relative
    access the walk admits, so a body without such a load has no data relocation.
    """
    from capstone.arm import ARM_OP_MEM, ARM_REG_PC
    for item in reached:
        if item.mnemonic != "ldr":
            continue
        for operand in item.operands:
            if operand.type == ARM_OP_MEM and operand.mem.base == ARM_REG_PC:
                offset = ((item.address + 4) & ~3) + operand.mem.disp - address
                if 0 <= offset <= len(data) - 4 and \
                        not address <= int.from_bytes(data[offset:offset + 4], "little") < address + len(data):
                    return True
    return False


def check_labels(schema, reached, address, data, thumb, calls):
    """Raise ValueError unless the frame, call and data labels are those match.py can derive from `reached`.

    calls: whether the report claims calls (a call schema, or a data schema with the call summary).
    """
    import match_evidence as evidence
    from match import uses_stack_frame
    framed = schema in (evidence.FRAMED_SCHEMA, evidence.FRAMED_LINKED_SCHEMA, evidence.FRAMED_DATA_SCHEMA)
    if (thumb and uses_stack_frame(reached)) != framed:
        raise ValueError("plain report frame label disagrees with the walk")
    called = any(item.mnemonic == "bl" and item.operands and
                 not address < item.operands[0].imm < address + len(data) for item in reached)
    if called != calls:
        raise ValueError("plain report call label disagrees with the walk")
    if schema in (evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA) and not data_literal(reached, address, data):
        raise ValueError("plain report data label has no literal word a data relocation could occupy")
