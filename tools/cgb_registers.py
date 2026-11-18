"""Prove the five switch-selected byte MMIO bindings in m4a's CgbSound."""

import re


SOURCE = "src/08145CAC.c"
HEADER = "include/ffta.h"
LOCALS = tuple(f"nrx{i}ptr" for i in range(5))
# NR10..14, NR21..24, NR30..34 and NR41..44. The second and fourth
# channels use the reserved bytes 0x61 and 0x71 as their unused first slot.
PORTS = ((0x60, 0x62, 0x63, 0x64, 0x65), (0x61, 0x68, 0x69, 0x6C, 0x6D),
         (0x70, 0x72, 0x73, 0x74, 0x75), (0x71, 0x78, 0x79, 0x7C, 0x7D))
TOKEN = re.compile(r"[A-Za-z_]\w*|0[xX][0-9A-Fa-f]+|[0-9]+|\S")
ENTRY = """void func_08145CAC(void) {
    s32 ch; struct MixerSource *channels; s32 prevC15;
    struct SoundMixerState *soundInfo = data_03007FF0;"""
LOOP = """s32 envelopeStepTimeAndDir; int mask = 0xff;
    if (soundInfo->cgbCounter15) soundInfo->cgbCounter15--;
    else soundInfo->cgbCounter15 = 14;
    for (ch = 1, channels = soundInfo->cgbChans; ch <= 4; ch++, channels++) {
        if (!(channels->status & SOUND_CHANNEL_SF_ON)) continue;
        switch (ch) {"""


def literal_defines(source, header):
    """The only inclusion is the base types. Source macros can emit numbers only."""
    for content in (source, header):
        if any(x in content for x in ("\\", "%:", "??", "<%", "%>", "\r", "\v", "\f")):
            return False
    directives = [line.strip() for line in header.splitlines() if "#" in line]
    if directives != ["#ifndef FFTA_H", "#define FFTA_H", "#endif"]:
        return False
    if not re.match(r"\s*#ifndef FFTA_H\s*#define FFTA_H\s+"
                    r"typedef\s+unsigned\s+char\s+u8\s*;", header):
        return False
    directives = [line.strip() for line in source.splitlines() if "#" in line]
    if not directives or directives[0] != '#include "ffta.h"':
        return False
    known = set()
    for directive in directives[1:]:
        definition = re.fullmatch(r"#define\s+([A-Z][A-Za-z0-9_]+)\s+(.+)", directive)
        if not definition or definition[1] in known:
            return False
        # The library defines integer constants and a parenthesized OR of
        # previously defined flags. Balanced syntax cannot move a statement.
        atom = r"(?:0x[0-9a-fA-F]+|[0-9]+|[A-Z][A-Za-z0-9_]+)"
        expression = definition[2]
        if not re.fullmatch(atom + r"|\(\s*" + atom + r"(?:\s*\|\s*" + atom + r")+\s*\)",
                            expression):
            return False
        if any(x[0].isupper() and x not in known for x in TOKEN.findall(expression)):
            return False
        known.add(definition[1])
    return True


def selected_offsets(text, code):
    """Every active path binds all five locals before their first dereference."""
    signature = list(re.finditer(r"\bvoid\s+func_08145CAC\s*\(", code))
    if len(signature) != 1:
        return set()
    start = signature[0].start()
    prefix = code[:start]
    if (prefix.count("{") != prefix.count("}") or any(name in prefix for name in LOCALS)
            or "#" in code[start:]):
        return set()
    matches = list(TOKEN.finditer(code, start))
    tokens = [item[0] for item in matches]
    cursor, qualifiers = 0, set()

    def consume(statement):
        nonlocal cursor
        expected = TOKEN.findall(statement)
        if tokens[cursor:cursor + len(expected)] != expected:
            return False
        for index, token in enumerate(expected):
            if token == "volatile":
                qualifiers.add(matches[cursor + index].start())
        cursor += len(expected)
        return True

    if not consume(ENTRY):
        return set()
    # Require an actual adjacent rationale for the complete pointer group.
    if cursor == len(matches) or not re.search(
            r"/\*\s*plausible:[^*]+\*/\s*$", text[:matches[cursor].start()]):
        return set()
    if not all(consume(f"volatile u8 *{name};") for name in LOCALS) or not consume(LOOP):
        return set()
    for index, ports in enumerate(PORTS):
        if not consume(f"case {index + 1}:" if index < 3 else "default:"):
            return set()
        for name, port in zip(LOCALS, ports):
            if not consume(f"{name} = (volatile u8 *)0x{0x04000000 + port:08X};"):
                return set()
        if not consume("break;"):
            return set()
    if not consume("}"):
        return set()

    # No second function, nested caller or uses outside this definition.
    depth = 2  # function and channel loop remain open
    for i in range(cursor, len(tokens)):
        if tokens[i] == "{":
            depth += 1
        elif tokens[i] == "}":
            depth -= 1
        if depth == 0 and i + 1 < len(tokens):
            return set()
    if depth:
        return set()
    used = set()
    # All subsequent references are direct byte loads or stores. The only
    # casts these offsets authorize are the twenty literal assignments above.
    for i in range(cursor, len(tokens)):
        name = tokens[i]
        if name not in LOCALS:
            continue
        if tokens[i-1] != "*":
            return set()
        before = tokens[i-2]
        if (before in ("{", "}", ";", ":", ")", "else") and tokens[i+1:i+2] == ["="] or
                name == "nrx2ptr" and before == "=" and tokens[i+1:i+2] == [";"] or
                name in ("nrx0ptr", "nrx3ptr") and before == "(" and
                tokens[i+1:i+4] == ["&", "0x08", ")"]):
            used.add(name)
        else:
            return set()
    return qualifiers if used == set(LOCALS) else set()
