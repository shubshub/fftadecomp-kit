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

A suspect finding is cleared by a comment containing `plausible:` on the same
line or the line above. Volatile additionally requires a direct I/O access or
a pointer used only for member access to an external symbol mapped into the
GBA I/O register window:

    /* plausible: hardware register, volatile is required here */
    *(volatile u16 *)0x04000000 = v;

The VSyncOn DMA counter has its own single-owner VBlank and compiler proof
(tools/m4a_dma_counter.py). Other volatile RAM is allowed only
for objects on the maintainer's volatile allow list (tools/volatile_allow.json),
and only inside the one listed header's anonymous `extern struct { ... }
symbol;` declaration, which must equal the pinned text, as qualifiers of
full-width bit-field members of listed types, while config/data_symbols.json
maps the symbol to the listed address.  Source files never qualify.  match.py
then compiles each user a second time with the qualifier stripped from that
declaration and refuses any difference beyond the documented dead load before
each member store (tools/volatile_semantics.py).

A qualifier of the addressed `src/<ADDR>.c` that is the SDK's BIOS fill
temporary, `volatile u16`/`u32` passed by address to CpuSet, or `volatile u32`
to CpuFastSet, with a fixed source, is admitted where the ROM shows that fill
(tools/bios_fill_temporary.py).

A qualifier of the addressed `src/<ADDR>.c` that none of these exceptions
admits is admitted where the ROM shows its effect (tools/volatile_rom_proof.py):
compiled with and without it, the plain build drops, merges or moves one of
its accesses, and every access reaches a hardware window, a cartridge-bus
address the function writes, or a shared object of tools/volatile_objects.json.

agbcc reads `volatile`, `__volatile__` and `__volatile` as the same qualifier
(kit#93).  The `volatile` rule refuses all three, and every exception above
accepts only the plain spelling; in a file with a line splice, an exception
holds only where it also holds with the splices joined.  Every asm keyword
spelling, a NUL byte and a preprocessor query (`__has_include`, `#embed`, ...)
are refused outright.  With --addr the addressed source's translation unit is
also checked after cpp (volatile_census): each qualifier the compiler will see
must be one this run read as a qualifier, in code, in a file it linted, and
the unit may hold no asm keyword.

A file with a line splice is checked twice, as written and with its splices
joined, and a finding of either view is a finding (kit#357).  The hardware
exception holds for a scalar direct access, or a bound register block, that
lies wholly inside the I/O window; with --addr the census also checks that
cpp leaves each qualifier it admits where it still holds.
"""

import argparse
import bisect
import functools
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import subprocess
import sys
import tempfile

JUSTIFY = "plausible:"

# Every spelling agbcc reads as the volatile qualifier: gcc/c-parse.gperf maps
# `volatile`, `__volatile__` and `__volatile` to TYPE_QUAL RID_VOLATILE.  Each
# check that looks for the qualifier uses VOLATILE (kit#93).
VOLATILE_SPELLINGS = ("volatile", "__volatile__", "__volatile")
VOLATILE = r"\b(?:__volatile__|__volatile|volatile)\b"
VOLATILE_QUALIFIER = re.compile(VOLATILE)
GNU_VOLATILE = ("`{}` is GNU C's spelling of volatile: the same qualifier, refused everywhere "
                "(every exception accepts only the plain spelling `volatile`)")

# id, severity, pattern, message
RULES = [
    # --- constructs that are a codegen hack by definition
    # `asm`, `__asm` and `__asm__` are all ASM_KEYWORD in agbcc's c-parse.gperf,
    # and its grammar takes any type qualifier before the `(`: the token itself
    # is refused (`__asm("")`, `asm const ("")`, `int r __asm("r4");`).
    ("inline-asm", "error", r"\b(?:__asm__|__asm|asm)\b",
     "inline assembly: the point of a matching decomp is C that compiles to the "
     "original code, not asm pasted into a C file"),
    # matched against the view that keeps string literals (check_view): the
    # code view blanks the quoted file name
    ("asm-include", "error", r'(?m)^[ \t]*#[ \t]*include[ \t]*["<][^">\n]*\.[sS][">]',
     "including an assembly file"),
    ("optimize-pragma", "error",
     r"#\s*pragma\s+(?:GCC\s+)?optimize\b|__attribute__\s*\(\(?[^)]*optimize",
     "optimisation pragma/attribute: changes code generation outside the source"),
    ("target-pragma", "error",
     r"#\s*pragma\s+(?:GCC\s+)?target\b|__attribute__\s*\(\(?[^)]*target",
     "target pragma/attribute: retargets code generation from inside the source"),
    ("stringised-pragma", "error", r"\b_Pragma\s*\(|\bpragma\s*\(\s*[A-Za-z_]",
     "_Pragma / stringised pragma: a banned directive written so that it does "
     "not read as one - say what it does, or drop it"),
    ("no-standard-errors", "error", r"#\s*pragma\s+GCC\s+diagnostic",
     "disabling diagnostics to silence warnings the original would not have"),
    ("dead-code", "error", r"\bif\s*\(\s*0\s*\)|\bwhile\s*\(\s*0\s*\)|#\s*if\s+0\b",
     "dead code whose only purpose is to steer the compiler"),
    ("empty-body", "error", r"\)\s*\{\s*\}",
     "empty function body"),
    ("placeholder", "error", r"\?\?\?|\bTODO\b|\bFIXME\b|\bUNIMPLEMENTED\b|not implemented",
     "placeholder body"),
    ("volatile", "error", VOLATILE,
     "volatile: it suppresses reordering, which is the classic way to force a "
     "byte match (real I/O code is the only legitimate use - justify it)"),
    ("attribute-steering", "error",
     r"__attribute__\s*\(\(\s*_?+(used|section|alias|weak|naked|constructor|destructor|retain|common)",
     "attribute that only affects code placement or emission"),
    ("emission-pragma", "error",
     r"#\s*pragma\s+(?:GCC\s+)?_?(used|weak|section|retain|common|extern_weak)\b",
     "pragma that forces a symbol to exist or where it lands: code placement "
     "and emission are not the programmer's business in a decompilation"),

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
HACK_VOCABULARY = next(pattern for rid, _, pattern, _ in RULES if rid == "hack-vocabulary")


# A backslash, optional horizontal whitespace and a newline: GCC's cpp splices
# the lines even with the whitespace (it only warns), so every scan must too.
# cpp counts a NUL byte as that whitespace as well.
SPLICE = r"\\[ \t\f\v\0]*\r?\n"


def join_splices(text):
    """translation phase 2, as the preprocessor does it"""
    return re.sub(SPLICE, "", text)


def lexical_spans(text):
    """(kind, start, end) of each comment ("comment") and string or character literal ("literal") in text.

    The one scanner the rules and the justifications share:
    strip_comments_and_strings blanks exactly these spans, and a justification
    is read only from a "comment" span, so a comment clears a finding only if
    the rules read it as a comment.  A `//` comment ends before its newline; a
    block comment runs to its `*/` or the end of the text; a literal runs to
    its closing quote (a backslash takes the next character with it) or the
    end of the text."""
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            start = i
            while i < n and text[i] != "\n":
                i += 1
            yield "comment", start, i
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            start = i
            while i < n and not (text[i] == "*" and i + 1 < n and text[i + 1] == "/"):
                i += 1
            i += 2
            yield "comment", start, min(i, n)
        elif c in "\"'":
            start, q = i, c
            i += 1
            while i < n and text[i] != q:
                i += 2 if text[i] == "\\" else 1
            i = min(i + 1, n)
            yield "literal", start, i
        else:
            i += 1


def strip_comments_and_strings(text):
    """replace comments and string/char literals with spaces, keeping offsets.

    A block comment's newlines become spaces too: cpp reads the comment as one
    space, so a directive goes on past one that spans lines.  The result
    therefore numbers lines differently from the text after such a comment; a
    line number is counted in the text itself, at the same offset."""
    out = list(text)
    for _, start, end in lexical_spans(text):
        out[start:end] = " " * (end - start)
    return "".join(out)


def comment_justification(text, start, end):
    """the justification the comment text[start:end] carries, on one line, or None.

    The comment's text must begin with `plausible:`, after the `//` or `/*` and
    any blanks, and go on to say something (a letter or a digit) that admits
    no steering (hack-vocabulary).  A block comment must be closed.  So
    `implausible:`, `not plausible:`, a `plausible:` later in the comment, a
    label or string literal spelling it, and a bare `plausible:` carry none.
    The result is `plausible: ` and the rest of the comment, each continuation
    line's leading `*` dropped and its blanks run together."""
    token = text[start:end]
    if token.startswith("//"):
        body = token[2:]
    elif token.startswith("/*") and len(token) >= 4 and token.endswith("*/"):
        body = token[2:-2]
    else:
        return None
    body = body.lstrip()
    if not body.startswith(JUSTIFY):
        return None
    first, *rest = body[len(JUSTIFY):].split("\n")
    words = " ".join([first] + [re.sub(r"^\s*\*", "", line) for line in rest]).split()
    why = " ".join(words)
    if not re.search(r"[A-Za-z0-9]", why) or re.search(HACK_VOCABULARY, why):
        return None
    return f"{JUSTIFY} {why}"


@functools.lru_cache(maxsize=8)
def comment_lines(text):
    """(first line, last line, justification or None) of each comment in text, in order (lexical_spans)"""
    newlines = [match.start() for match in re.finditer("\n", text)]
    return tuple((bisect.bisect_left(newlines, start) + 1, bisect.bisect_left(newlines, max(start, end - 1)) + 1,
                  comment_justification(text, start, end))
                 for kind, start, end in lexical_spans(text) if kind == "comment")


def justification(text, line_no):
    """the justification of the first comment that carries one and lies on line_no or ends on the line before.

    Only a comment as lexical_spans reads it counts: its first line to its last
    must include line_no, or its last line must be the one before it."""
    for first, last, why in comment_lines(text):
        if first > line_no:
            break
        if why is not None and (first <= line_no <= last or last == line_no - 1):
            return why
    return None


def justified(text, line_no):
    """True if a comment that begins `plausible:` and says why covers this line (justification).

    Not the substring on the line: a label, a string literal, `implausible:`
    or an empty marker clears nothing."""
    if JUSTIFY not in text:
        # every justification spells the marker
        return False
    return justification(text, line_no) is not None


# The hardware-register exception (kit#357): a justified `volatile` is exempt
# only where every access through it stays inside the I/O window
# [0x04000000, IO_END).  The direct form `*(volatile T *)ADDR` admits only a
# scalar T, in a context the address walk (access_context) knows keeps the
# access a value; the bound form `volatile T *local = &symbol;` admits a scalar
# T or a struct of scalars and pointers defined in the same text, which must
# fit in the window from the symbol's mapped address.
IO_START, IO_END = 0x04000000, 0x04000400
SCALAR_SIZES = {"u8": 1, "s8": 1, "u16": 2, "s16": 2, "u32": 4, "s32": 4}
BUILTIN_SIZES = {("char",): 1, ("short",): 2, ("short", "int"): 2, ("int",): 4,
                 ("long",): 4, ("long", "int"): 4, (): 4}
HARDWARE_TYPE = r"(?:struct\s+|union\s+)?[A-Za-z_]\w*(?:\s+[A-Za-z_]\w*)*"
HARDWARE_DIRECT = re.compile(r"\*\s*\(\s*(?P<v>volatile)\s+(?P<type>" + HARDWARE_TYPE +
                             r")\s*\*\s*\)\s*(?P<address>0x[0-9a-fA-F]+)[uUlL]*\b(?=\s*(?:[;=),]|$))")
HARDWARE_BOUND = re.compile(r"\b(?P<v>volatile)\s+(?P<type>" + HARDWARE_TYPE +
                            r")\s*\*\s*(?:const\s+)?(?P<local>[A-Za-z_]\w*)\s*=\s*"
                            r"&\s*(?P<symbol>[A-Za-z_]\w*)\s*;")


def scalar_size(ctype):
    """the size of the scalar integer type spelt ctype, or None"""
    words = ctype.split()
    if len(words) == 1 and words[0] in SCALAR_SIZES:
        return SCALAR_SIZES[words[0]]
    if words and words[0] in ("signed", "unsigned"):
        words = words[1:]
    elif not words:
        return None
    return BUILTIN_SIZES.get(tuple(words))


QUALIFIER_WORDS = {"const", "volatile"}
TYPE_WORDS = {"signed", "unsigned", "char", "short", "int", "long", "void", "float", "double",
              "struct", "union", "enum"} | QUALIFIER_WORDS
IDENTIFIER = re.compile(r"[A-Za-z_]\w*")
DIRECTIVE = re.compile(r"(?m)^[ \t]*#(?:\\\n|[^\n])*")
# a declaration's specifiers that are neither a type nor a declarator
SPECIFIER_WORDS = {"typedef", "extern", "static", "auto", "register", "inline", "__inline", "__inline__",
                   "__extension__", "__const", "__const__", "__volatile", "__volatile__", "__restrict",
                   "__restrict__"} | QUALIFIER_WORDS
TYPEOF_WORDS = {"typeof", "__typeof", "__typeof__"}


def blank_directives(text):
    """text with every preprocessor directive, splices included, blanked to spaces"""
    return DIRECTIVE.sub(lambda directive: re.sub(r"[^\n]", " ", directive[0]), text)


def strip_attributes(text):
    """text with every `__attribute__((...))` blanked, however deep its parentheses"""
    out = list(text)
    for word in re.finditer(r"\b__attribute(?:__)?\b", text):
        index = word.end()
        while index < len(text) and text[index].isspace():
            index += 1
        depth, end = 0, index
        while end < len(text) and text[index] == "(":
            depth += (text[end] == "(") - (text[end] == ")")
            end += 1
            if depth <= 0:
                break
        out[word.start():end] = " " * (end - word.start())
    return "".join(out)


def declaration_start(code, position):
    """the offset where the declaration holding position begins: after the previous `;`, block `{` or `}`"""
    index = position
    while index > 0:
        char = code[index - 1]
        if char in ")]}":
            opener, depth, open_ = {")": "(", "]": "[", "}": "{"}[char], 0, None
            for back in range(index - 1, -1, -1):
                depth += (code[back] == char) - (code[back] == opener)
                if depth == 0:
                    open_ = back
                    break
            if open_ is None:
                return index
            if char == "}" and not re.search(r"\b(?:struct|union|enum)\s*(?:[A-Za-z_]\w*\s*)?\Z", code[:open_]):
                return index
            index = open_
            continue
        if char in ";{([":
            return index
        index -= 1
    return 0


@functools.lru_cache(maxsize=16)
def typedef_declarations(code):
    """((name, declaration), ...) for every name a typedef in code declares, wherever `typedef` stands.

    C lets `typedef` stand anywhere among the specifiers (`unsigned char
    typedef u8;`), so each declaration is read whole, from its start.
    Attributes are blanked for the parse, so one between `struct` and its
    body does not hide where the declaration starts, but each declaration is
    returned as written, so `__attribute__((mode(DI)))` keeps a typedef from
    reading as canonical.
    """
    raw = blank_directives(code)
    code = strip_attributes(raw)
    found = []
    for match in re.finditer(r"\btypedef\b", code):
        start = declaration_start(code, match.start())
        depth, end = 0, match.end()
        while end < len(code) and not (code[end] == ";" and depth <= 0):
            depth += code[end] in "({[" or -(code[end] in ")}]")
            end += 1
        tokens = re.findall(r"[A-Za-z_]\w*|\S", code[start:end])
        position, typed = 0, False
        while position < len(tokens):
            token = tokens[position]
            if token in ("struct", "union", "enum") or token in TYPEOF_WORDS:
                typed, position = True, position + 1
                if token not in TYPEOF_WORDS and position < len(tokens) and IDENTIFIER.fullmatch(tokens[position]):
                    position += 1
                if position < len(tokens) and tokens[position] in ("{", "("):
                    depth = 0
                    while position < len(tokens):
                        depth += (tokens[position] in "{(") - (tokens[position] in "})")
                        position += 1
                        if depth == 0:
                            break
            elif token in SPECIFIER_WORDS:
                position += 1
            elif token in TYPE_WORDS:
                typed, position = True, position + 1
            elif not typed and IDENTIFIER.fullmatch(token):
                typed, position = True, position + 1
            else:
                break
        depth, named = 0, False
        for token in tokens[position:]:
            if token in ("(", "["):
                depth += 1
            elif token in (")", "]"):
                depth -= 1
            elif token == "," and depth == 0:
                named = False
            elif not named and IDENTIFIER.fullmatch(token) and token not in SPECIFIER_WORDS:
                found.append((token, raw[start:end + 1]))
                named = True
    return tuple(found)


def names_hold(code, ctype, unit=False):
    """do the names in ctype mean in code what the size rules assume (kit#357)?

    A scalar name (u8 .. s32) may only be declared by a typedef of a builtin
    integer type of its size, `typedef unsigned short u16;`: a typedef in a
    block, or in a file without ffta.h, could make it an array or a struct.  In
    a preprocessed translation unit (unit) it must be declared exactly once.  A
    struct's typedef name must be declared exactly once.
    """
    declared = typedef_declarations(code)
    for word in ctype.split():
        if word in SCALAR_SIZES:
            declarations = [statement.strip() for name, statement in declared if name == word]
            for statement in declarations:
                canonical = re.fullmatch(r"typedef\s+(?P<words>(?:signed|unsigned|char|short|int|long)"
                                         r"(?:\s+(?:signed|unsigned|char|short|int|long))*)\s+" + word +
                                         r"\s*;", statement)
                if canonical is None or scalar_size(canonical["words"]) != SCALAR_SIZES[word]:
                    return False
            if unit and len(declarations) != 1:
                return False
    if IDENTIFIER.fullmatch(ctype) and scalar_size(ctype) is None:
        return sum(name == ctype for name, _ in declared) == 1
    return True


def struct_size(code, ctype, unit=False):
    """agbcc's size for the struct ctype names, from its one definition in code.

    None unless every member is a scalar integer or a pointer, declared one to
    a declaration: no arrays, bit-fields, nested types or unknown typedefs, and
    every scalar name a member uses holds (names_hold).  Members are aligned to
    their size, and the struct is rounded up to a multiple of 4, as agbcc
    rounds every struct (STRUCTURE_SIZE_BOUNDARY 32).
    """
    tag = re.fullmatch(r"struct\s+([A-Za-z_]\w*)", ctype)
    if tag:
        heads = [match.end() for match in re.finditer(r"\bstruct\s+" + tag[1] + r"\s*\{", code)]
    elif IDENTIFIER.fullmatch(ctype):
        heads = []
        for match in re.finditer(r"\btypedef\s+struct\s*(?:[A-Za-z_]\w*\s*)?\{", code):
            close = code.find("}", match.end())
            if close >= 0 and re.match(r"\s*" + re.escape(ctype) + r"\s*;", code[close + 1:]):
                heads.append(match.end())
    else:
        return None
    if len(heads) != 1:
        return None
    close = code.find("}", heads[0])
    if close < 0:
        return None
    offset = 0
    for member in code[heads[0]:close].split(";"):
        if not member.strip():
            continue
        match = re.fullmatch(r"\s*(?:const\s+)?(?P<type>[A-Za-z_]\w*(?:\s+[A-Za-z_]\w*)*?)\s*"
                             r"(?P<pointer>\*+\s*(?:const\s*)?)?(?P<name>[A-Za-z_]\w*)\s*", member)
        if match is None or not all(names_hold(code, word, unit) for word in match["type"].split()
                                    if word in SCALAR_SIZES):
            return None
        size = 4 if match["pointer"] else scalar_size(match["type"])
        if size is None:
            return None
        offset = (offset + size - 1) // size * size + size
    return (offset + 3) // 4 * 4 if offset else None


DIGRAPHS = {"<:": "[ ", ":>": " ]", "<%": "{ ", "%>": " }", "%:%:": "##  ", "%:": "# "}


def spell_digraphs(code, view=None):
    """code (comments and literals already blanked) with each digraph spelt as its bracket or `#`.

    cpp and agbcc read `%:` as `#`, `<%` as `{` and `<:` as `[` (kit#408).
    Outside a literal no valid C has these pairs otherwise, and the offsets
    are kept.  Given view, another view of the same text (one that keeps its
    literals, say), the digraphs code holds are spelt in view instead, so a
    literal's text is left as it is.
    """
    out = list(code if view is None else view)
    for digraph in re.finditer(r"%:%:|<:|:>|<%|%>|%:", code):
        out[digraph.start():digraph.end()] = DIGRAPHS[digraph[0]]
    return "".join(out)


def operand_view(text):
    """text with comments blanked and every literal filled with `0`, keeping offsets.

    In the code view a literal is blank, so `'c' & x` reads as a unary `&`; here
    the literal is still an operand.  Digraphs are spelt as what they stand for.
    """
    code = strip_comments_and_strings(text)
    out = list(code)
    for literal in re.finditer(r'"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\'', text):
        if code[literal.start()] == " " and not code[literal.start():literal.end()].strip():
            out[literal.start():literal.end()] = "0" * (literal.end() - literal.start())
    return spell_digraphs("".join(out))


# The address walk (kit#357).  It reads tokens, never a fixed window, and it
# is a whitelist: from the access it steps outward only through what can keep
# an lvalue (parentheses, casts, the comma operator GNU C lets stand as an
# lvalue, the conditional operator, and the transparent keywords), and it
# admits only a context it knows makes the access a value: an operator, an
# assignment, a call's argument, a condition or a statement.  Anything else it
# does not model, such as `sizeof`, `__typeof__`, a name or a stray token,
# refuses.
STATEMENT_WORDS = {"return", "case", "else", "do"}
CONTROL_WORDS = {"if", "while", "for", "switch"}
LVALUE_WORDS = {"__extension__", "__real__", "__real", "__imag__", "__imag"}
SIZE_WORDS = {"sizeof", "__alignof__", "__alignof"}
KEYWORDS = TYPE_WORDS | STATEMENT_WORDS | CONTROL_WORDS | LVALUE_WORDS | SIZE_WORDS | SPECIFIER_WORDS | \
    TYPEOF_WORDS | {"break", "continue", "default", "goto", "asm"}
VALUE_TOKENS = {"=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=", "&=", "^=", "|=", "+", "-", "*", "/", "%",
                "<<", ">>", "<", ">", "<=", ">=", "==", "!=", "^", "|", "&&", "||", "!", "~", "++", "--",
                "[", ";", "{", "}"} | STATEMENT_WORDS
OPENERS = {")": "(", "]": "[", "}": "{"}
NUMBER = re.compile(r"\.?\d")
WALK_TOKEN = re.compile(r"[A-Za-z_$][\w$]*|\.?\d(?:[eEpP][-+]|[\w.])*|->|\+\+|--|<<=|>>=|\.\.\.|##|"
                        r"[-+*/%&|^!=<>]=|<<|>>|&&|\|\||\S")


class WalkRun:
    """a run of tokens with their offsets, matching brackets and innermost open bracket"""

    def __init__(self, text, begin, end):
        tokens = list(WALK_TOKEN.finditer(text, begin, end))
        self.starts = [token.start() for token in tokens]
        self.texts = [token[0] for token in tokens]
        self.partner = [None] * len(tokens)
        self.enclosing = [None] * len(tokens)
        stack = []
        for index, token in enumerate(self.texts):
            self.enclosing[index] = stack[-1] if stack else None
            if token in ("(", "[", "{"):
                stack.append(index)
            elif token in OPENERS and stack and self.texts[stack[-1]] == OPENERS[token]:
                self.partner[index] = stack.pop()
                self.partner[self.partner[index]] = index


@functools.lru_cache(maxsize=8)
def walk_runs(view):
    """(the code's tokens, directive starts, (start, end, the body's tokens) per directive) of a view.

    Directives are not code: a macro's body is walked on its own, from its
    start, and the census walks what cpp made of it.  Splices are whitespace.
    """
    spliced = view.replace("\\\n", "  ")
    directives = [(directive.start(), directive.end()) for directive in DIRECTIVE.finditer(view)]
    bodies = []
    for start, end in directives:
        head = re.match(r"[ \t]*#[ \t]*(?:define[ \t]+[A-Za-z_]\w*(?:\([^)]*\))?|[A-Za-z_]\w*)?", spliced[start:end])
        bodies.append((start, end, WalkRun(spliced, start + head.end(), end)))
    return WalkRun(blank_directives(spliced), 0, len(view)), [start for start, _ in directives], bodies


def walk_position(view, offset):
    """(run, index) of the token that starts at offset, or None"""
    code, starts, bodies = walk_runs(view)
    run = code
    directive = bisect.bisect_right(starts, offset) - 1
    if directive >= 0 and offset < bodies[directive][1]:
        run = bodies[directive][2]
    index = bisect.bisect_left(run.starts, offset)
    return (run, index) if index < len(run.starts) and run.starts[index] == offset else None


def is_name(token, typedefs):
    """is token an object's or a function's name: an identifier that is no keyword or type?"""
    return (IDENTIFIER.fullmatch(token) is not None and token not in KEYWORDS and not token.startswith("__")
            and token not in SCALAR_SIZES and (typedefs is None or token not in typedefs))


def control_header(run, open_):
    return open_ > 0 and run.texts[open_ - 1] in CONTROL_WORDS


def type_name(run, open_, typedefs):
    """does the group opened at open_ hold only a type name?"""
    close = run.partner[open_]
    tokens = run.texts[open_ + 1:close] if close is not None else []
    if not tokens or any(not (IDENTIFIER.fullmatch(token) or token == "*") for token in tokens):
        return False
    names = [token for token in tokens if token != "*" and token not in QUALIFIER_WORDS]
    if any(name in TYPE_WORDS for name in names):
        return True
    return len(names) == 1 and (typedefs is None or names[0] in typedefs or names[0] in SCALAR_SIZES)


def is_cast(run, open_, typedefs):
    """is the group opened at open_ a cast's type name?  None when the brackets do not match.

    typedefs, the names that are types, tells a cast `(T)` from a
    parenthesized operand `(x)`; without it a lone name counts as a type.
    """
    while True:
        if not type_name(run, open_, typedefs):
            return False
        if open_ == 0:
            return True
        token = run.texts[open_ - 1]
        if token == ")":
            inner = run.partner[open_ - 1]
            if inner is None:
                return None
            if control_header(run, inner):
                return True
            open_ = inner
            continue
        if IDENTIFIER.fullmatch(token):
            return token in STATEMENT_WORDS or token in LVALUE_WORDS
        return not (token in ("]", "++", "--") or NUMBER.match(token))


def operand_end(run, index, typedefs):
    """does the token at index end an operand, so that a `&` or `*` after it is binary?"""
    if index < 0:
        return False
    token = run.texts[index]
    if token == ")":
        open_ = run.partner[index]
        return open_ is not None and is_cast(run, open_, typedefs) is False and not control_header(run, open_)
    return token in ("]", "++", "--") or NUMBER.match(token) is not None or is_name(token, typedefs)


def converts_to_value(view, run, ampersand, typedefs):
    """is the unary `&` at ampersand at once the operand of a cast to `void *` or to an integer type?

    Such a value carries no volatile qualifier: nothing reaches memory through
    it without a new cast, and a new volatile cast is a qualifier of its own,
    exempt only as a direct access to a literal address.  So a register's
    address passed on as a DMA source or destination is admitted.
    """
    close = ampersand - 1
    if close < 0 or run.texts[close] != ")":
        return False
    open_ = run.partner[close]
    if open_ is None or not is_cast(run, open_, typedefs):
        return False
    content = " ".join(run.texts[open_ + 1:close])
    if re.fullmatch(r"(?:const )?void \*", content):
        return True
    return ("*" not in content.split() and scalar_size(content) is not None and
            all(names_hold(view, word, typedefs is not None) for word in content.split() if word in SCALAR_SIZES))


def access_context(view, start, typedefs=None):
    """why the operand whose first token is at start may not be a plain access, or None if it is (kit#357).

    "address" when a unary `&` reaches it through parentheses, casts, comma
    or conditional operators or a transparent keyword, unless the address is
    converted at once to a value (converts_to_value); "unknown" when the walk
    meets a context it does not model.  view is operand_view's; typedefs is
    given for a preprocessed unit (is_cast).
    """
    position = walk_position(view, start)
    if position is None:
        return "unknown"
    run, node = position
    group = False
    while True:
        before = node - 1
        if before < 0:
            return None
        token = run.texts[before]
        if token == ")":
            open_ = run.partner[before]
            cast = None if open_ is None else is_cast(run, open_, typedefs)
            if cast:
                node = open_
                continue
            if cast is not None and (control_header(run, open_) or group):
                return None
            return "unknown"
        if token in LVALUE_WORDS:
            node = before
            continue
        if token == "&":
            if operand_end(run, before - 1, typedefs):
                return None
            return None if converts_to_value(view, run, before, typedefs) else "address"
        if token in VALUE_TOKENS:
            return None
        if token == "(":
            node, group = before, True
            continue
        if token in (",", "?", ":"):
            outer = run.enclosing[before]
            if outer is None or run.texts[outer] != "(":
                return None
            node, group = outer, True
            continue
        if group and (token == "]" or token in CONTROL_WORDS or is_name(token, typedefs)):
            return None
        return "unknown"


def direct_access_holds(code, match, view=None, typedefs=None):
    """does a HARDWARE_DIRECT match access exactly a register inside the I/O window?"""
    size = scalar_size(match["type"])
    address = int(match["address"], 16)
    return (size is not None and IO_START <= address and address + size <= IO_END and
            names_hold(join_splices(code), match["type"], typedefs is not None) and
            access_context(view if view is not None else operand_view(code), match.start(), typedefs) is None)


def bound_target_holds(code, match, data_symbols, unit=False):
    """is a HARDWARE_BOUND binding's symbol mapped in the window, with the whole pointed-to type inside it?"""
    value = data_symbols.get(match["symbol"])
    try:
        address = int(value, 0) if isinstance(value, str) else int(value)
    except (TypeError, ValueError):
        return False
    joined = join_splices(code)
    size = scalar_size(match["type"]) or struct_size(joined, match["type"], unit)
    return (size is not None and IO_START <= address and address + size <= IO_END and
            names_hold(joined, match["type"], unit))


def bound_use_holds(code, ref, view=None, typedefs=None):
    """is this use of a bound MMIO pointer an immediate member access or dereference, in a plain access?"""
    view = view if view is not None else operand_view(code)
    position = walk_position(view, ref.start())
    if position is None:
        return False
    run, index = position
    texts = run.texts
    if index + 2 < len(texts) and texts[index + 1] == "->" and IDENTIFIER.fullmatch(texts[index + 2]):
        return access_context(view, ref.start(), typedefs) is None
    # a lone name in parentheses before the `*` counts as an operand here, unless the unit's
    # typedefs say it is a type: `(factor) * port` must not read as a dereference
    if index > 0 and texts[index - 1] == "*" and \
            not operand_end(run, index - 2, typedefs if typedefs is not None else frozenset()):
        after = texts[index + 1] if index + 1 < len(texts) else None
        return (after not in ("[", "(", "++", "--", "+=", "-=", "->", ".") and
                access_context(view, run.starts[index - 1], typedefs) is None)
    return False


def symbol_holds(code, symbol):
    """is every occurrence of symbol in code an `extern` declaration of it, or the operand of `&`?"""
    declarations = [match.span() for match in re.finditer(
        r"(?m)^\s*extern\s+" + HARDWARE_TYPE + r"\s+" + re.escape(symbol) + r"\s*;", code)]
    return bool(declarations) and all(
        any(start <= ref.start() < end for start, end in declarations) or
        re.search(r"&\s*\Z", code[max(0, ref.start() - 64):ref.start()])
        for ref in re.finditer(r"\b" + re.escape(symbol) + r"\b", code))


def hardware_volatile_offsets(text, code, data_symbols):
    """Recognize documented, directly bound MMIO qualifiers, not local steering."""
    allowed = set()
    if not re.search(r"\bvolatile\b", code):
        return allowed
    code = spell_digraphs(code)
    view = operand_view(text)

    def justified_io(offset, address):
        # the same justification a suspect needs (justified: the shared comment scanner)
        return IO_START <= address < IO_END and justified(text, text.count("\n", 0, offset) + 1)

    for match in HARDWARE_DIRECT.finditer(code):
        if direct_access_holds(code, match, view) and justified_io(match.start("v"), int(match["address"], 16)):
            allowed.add(match.start("v"))

    ctype = HARDWARE_TYPE
    bindings = list(HARDWARE_BOUND.finditer(code))
    for match in bindings:
        symbol = match["symbol"]
        value = data_symbols.get(symbol)
        try:
            address = int(value, 0) if isinstance(value, str) else int(value)
        except (TypeError, ValueError):
            continue
        declaration = re.search(r"(?m)^\s*extern\s+" + ctype + r"\s+" +
                                re.escape(symbol) + r"\s*;", code)
        if declaration is None:
            continue
        # Reject shadow declarations, pointer retargeting and pointer escapes.
        references = list(re.finditer(r"\b" + re.escape(symbol) + r"\b", code))
        if any(not declaration.start() <= ref.start() < declaration.end() and
               not re.search(r"&\s*$", code[:ref.start()]) for ref in references):
            continue
        local_uses = re.finditer(r"\b" + re.escape(match["local"]) + r"\b", code)
        declarations = [item.span("local") for item in bindings
                        if item["local"] == match["local"]]
        if any(ref.span() not in declarations and not bound_use_holds(code, ref, view)
               for ref in local_uses):
            continue
        if bound_target_holds(code, match, data_symbols) and justified_io(match.start("v"), address):
            allowed.add(match.start("v"))
    return allowed


def exempt_shape_holds(code, offset, data_symbols, view=None, typedefs=None):
    """does the qualifier at offset of a preprocessed unit sit where the hardware exception holds?

    The census's placement check (kit#357), on the whole unit, so every typedef
    and macro is in view: the qualifier must begin a direct access that holds,
    or a binding that holds, whose symbol is the extern object (never
    redeclared) and whose every later use in its block is a member access or
    dereference whose address is never taken.  The justification was checked
    where the qualifier is written; a macro can move it, not justify it.
    """
    view = view if view is not None else code
    window = code[max(0, offset - 256):offset]
    prefix = re.search(r"\*\s*\(\s*\Z", window)
    if prefix:
        match = HARDWARE_DIRECT.match(code, offset - len(window) + prefix.start())
        if match and match.start("v") == offset and direct_access_holds(code, match, view, typedefs):
            return True
    match = HARDWARE_BOUND.match(code, offset)
    if match is None or not bound_target_holds(code, match, data_symbols, typedefs is not None) or \
            not symbol_holds(code, match["symbol"]):
        return False
    depth, end = 0, len(code)
    for index in range(match.end(), len(code)):
        if code[index] == "{":
            depth += 1
        elif code[index] == "}":
            depth -= 1
            if depth < 0:
                end = index
                break
    local = re.compile(r"\b" + re.escape(match["local"]) + r"\b")
    return all(bound_use_holds(code, ref, view, typedefs) for ref in local.finditer(code, match.end(), end))


def volatile_allow_path():
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), "volatile_allow.json")


def volatile_allow_entries():
    """the maintainer's volatile allow list; unreadable or malformed is empty"""
    try:
        doc = json.loads(Path(volatile_allow_path()).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return []
    entries = doc.get("entries") if isinstance(doc, dict) else None
    return entries if isinstance(entries, list) else []


def declaration_tokens(code):
    """C tokens of a declaration, so the pinned text ignores only whitespace"""
    return re.findall(r"[A-Za-z_]\w*|0[xX][0-9A-Fa-f]+|[0-9]+|\S", code)


def declares_symbol(code, symbol):
    """a file-scope `extern` declarator of the symbol in this file.

    Such a file cannot also see the listed volatile declaration (the types
    would conflict), so it is not a user of it.  Only a depth-0 `extern`
    whose declarator list names the symbol outside any parentheses counts;
    a parameter name in a prototype does not.
    """
    declarator = re.compile(r"extern\b(?:[^;{}()]|\{[^{}]*\})*?\b" + re.escape(symbol) +
                            r"\s*[;,=\[]")
    for keyword in re.finditer(r"\bextern\b", code):
        prefix = code[:keyword.start()]
        if prefix.count("{") == prefix.count("}") and declarator.match(code, keyword.start()):
            return True
    return False


def active_volatile_entries(data_symbols, entries):
    """entries whose symbol the data map binds to exactly the listed address"""
    active = []
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        symbol, address, header, types, declaration = (
            entry.get("symbol"), entry.get("address"), entry.get("header"),
            entry.get("member_types"), entry.get("declaration"))
        if not (isinstance(symbol, str) and re.fullmatch(r"[A-Za-z_]\w*", symbol) and
                isinstance(address, str) and isinstance(header, str) and
                isinstance(declaration, str) and
                isinstance(types, list) and types and
                all(isinstance(t, str) and re.fullmatch(r"[A-Za-z_]\w*", t) for t in types)):
            continue
        mapped = data_symbols.get(symbol)
        try:
            if int(mapped, 0) != int(address, 0):
                continue
        except (TypeError, ValueError):
            continue
        active.append(entry)
    return active


def allowlisted_volatile(code, relpath, data_symbols, entries, text=None, closure=None,
                         untranslated=None, tree=None):
    """(exempt volatile offsets, findings) for the volatile allow list.

    Only the listed header may hold the listed object's declaration, and its
    tokens must equal the entry's pinned `declaration`: one file-scope
    anonymous `extern struct { ... } symbol;`.  Inside its braces, `volatile`
    may only begin a bit-field member `volatile T name : N;` with T a listed
    member type.  Bit-fields have no address, and the braces hold no nested,
    tagged or parenthesized types, so the qualifier cannot reach any other
    object.  The bit-field must be full width for its type (`u8 : 8`,
    `u16 : 16`; BIT_FIELD_WIDTHS), the members the semantic check models.

    While the entry is active, every linted file is scanned with line splices
    joined as cpp joins them, and refuses: form feed, vertical tab, NUL and lone
    carriage return; #include
    outside include/ and src/*.h (from the closure); token pasting, digraph and trigraph spellings (they
    can build a directive or name the scan cannot see); typeof (it would copy
    the qualifier onto locals); #line, linemarkers, #import, #include_next
    and computed #include (they hide or fake dependencies); #define/#undef of
    any identifier of the pinned declaration or the entry's include guard;
    and any #define whose
    replacement names the symbol.  Other headers may not name the symbol, and
    every use must be immediate member access `symbol.member`, so neither its
    address nor the whole object can reach pointer arithmetic, a macro
    argument or a copy.  The exceptions are kit#375's rule U
    (whole_object_sites): `sizeof symbol`, and `&symbol` as one complete
    argument at a `void *` / `const void *` parameter of a prototyped callee
    or typed function-pointer table element; and rule P (typed_pointer_sites):
    one block-scope `__typeof__(symbol) *name` bound once to `&symbol` and used
    only as `name->member` or as such an argument.  Only a file with its own file-scope declarator whose
    include closure (closure=(inside, outside)) provably misses the listed
    header is exempt; without a closure nothing is.

    These rules keep the pinned declaration's text intact through the
    preprocessor, which match.py's semantic check relies on: it strips
    `volatile` from exactly that declaration and refuses any difference
    beyond the qualifier's documented effect (tools/volatile_semantics.py).
    Planted reads and self-assignments are refused there, not here.
    """
    allowed, findings = set(), []

    def finding(offset, message):
        # offsets index source; its comments keep their newlines
        findings.append((source.count("\n", 0, min(offset, len(source))) + 1,
                         "volatile-allowlist", "error", message))

    source = join_splices(text if text is not None else code)
    joined = strip_comments_and_strings(source)
    raw = strip_comments_and_strings_keep_strings(source)
    inside, outside = closure if closure is not None else (None, [])
    for entry in active_volatile_entries(data_symbols, entries):
        symbol, header = entry["symbol"], entry["header"]
        pinned = declaration_tokens(entry["declaration"])
        lexical = (r"##|%:", "token pasting, digraphs and trigraphs")
        for match in list(re.finditer(lexical[0], joined)) + \
                list(re.finditer(r"\?\?[=/'()!<>\-]", text if text is not None else code)):
            finding(match.start(), f"{lexical[1]} are refused while {symbol} is an "
                    "allowlisted volatile object: they can spell what the scan cannot see")
        # `#` only belongs on a directive line; anywhere else (`F(#) pragma`)
        # it can be pasted into a forged directive or linemarker.
        for line in re.finditer(r"(?m)^[^\n]*", joined):
            if line[0].lstrip().startswith("#"):
                continue
            for hash_token in re.finditer(r"#", line[0]):
                finding(line.start() + hash_token.start(), f"`#` outside a directive line is "
                        f"refused while {symbol} is allowlisted: it could forge a directive")
        for control in re.finditer(r"[\f\v\0]|\r(?!\n)", untranslated if untranslated is not None
                                   else text if text is not None else code):
            finding(control.start(), f"form feed, vertical tab, NUL and lone carriage return are "
                    f"refused while {symbol} is allowlisted: cpp treats them as whitespace "
                    "where the directive scans do not")
        # kit#375: the prototypes of this file and its headers (rules U and P)
        context = [joined]
        for included in sorted(inside or ()):
            if included in (relpath, header) or tree is None:
                continue
            try:
                context.append(strip_comments_and_strings(join_splices(
                    (Path(tree) / included).read_text(encoding="utf-8", errors="replace"))))
            except OSError:
                pass            # reported below
        fragments = declaration_fragments("\n;\n".join(context))
        # kit#375, rule P: one typed pointer to the object, bound once to its address
        typed_admitted, typed_typeofs, typed_findings = ({}, set(), []) if relpath is None or \
            relpath.endswith(".h") else typed_pointer_sites(joined, symbol, entry["declaration"], fragments)
        # rule T: one typed copy in a struct member, saved from the object and read by member
        if not typed_typeofs and relpath is not None and not relpath.endswith(".h"):
            typed_admitted, typed_typeofs, typed_findings = typed_copy_sites(joined, symbol, entry["declaration"])
        for typeof in re.finditer(r"\b(?:typeof|__typeof|__typeof__)\b", joined):
            if typeof.start() in typed_typeofs:
                continue
            finding(typeof.start(), f"typeof while {symbol} is an allowlisted volatile "
                    "object: it would copy the qualifier onto other objects")
        for directive in re.finditer(r"(?m)^[ \t]*#[ \t]*(?:line\b|[0-9]|import\b|include_next\b)",
                                     joined):
            finding(directive.start(), f"#line, linemarkers, #import and #include_next are "
                    f"refused while {symbol} is allowlisted: they hide or fake dependencies")
        for include in re.finditer(r"(?m)^[ \t]*#[ \t]*include\b(?![ \t]*[\"<])", raw):
            finding(include.start(), f"computed #include is refused while {symbol} is allowlisted")
        names = {token for token in pinned if re.fullmatch(r"[A-Za-z_]\w*", token)}
        if isinstance(entry.get("guard"), str):
            names.add(entry["guard"])
        directives = list(re.finditer(
            r"(?m)^[ \t]*#[ \t]*(?P<kind>define|undef)[ \t]+(?P<name>[A-Za-z_]\w*)(?P<rest>[^\n]*)",
            joined))
        # The listed header itself defines its guard once, with no replacement.
        guard_definitions = [d for d in directives if d["name"] == entry.get("guard")]
        own_guard = (relpath == header and len(guard_definitions) == 1 and
                     guard_definitions[0]["kind"] == "define" and
                     not guard_definitions[0]["rest"].strip())
        for directive in directives:
            if directive["name"] in names and not (own_guard and directive["name"] == entry["guard"]):
                finding(directive.start(), f"`{directive['name']}` is part of the pinned {symbol} "
                        "declaration and may not be redefined while it is allowlisted")
            if directive["kind"] == "define" and re.search(r"\b" + re.escape(symbol) + r"\b",
                                                           directive["rest"]):
                finding(directive.start(), f"a macro may not expand to allowlisted volatile {symbol}")
            if directive["kind"] == "define" and forges_directive(directive["rest"]):
                finding(directive.start(), f"a macro may not expand to `#` while {symbol} is "
                        "allowlisted: it could forge a linemarker or directive")
        for escape in outside:
            finding(0, f"#include of `{escape}` leaves include/ and src/*.h, which are the "
                    f"only linted inputs, while {symbol} is allowlisted")
        references = list(re.finditer(r"\b" + re.escape(symbol) + r"\b", joined))
        if relpath is None or not relpath.endswith(".h"):
            # A file's own declaration exempts it only when it provably cannot
            # see the listed one: the header is outside its include closure.
            # The provenance rules bind users of the object only: files that
            # name the symbol or reach the listed header.  Other sources cannot
            # see the qualifier, and the rules would refuse ordinary C there.
            uses = (inside is not None and header in inside) or bool(references)
            if uses and not (declares_symbol(joined, symbol) and inside is not None
                             and header not in inside):
                # kit#375, rule U: `sizeof symbol` and `&symbol` as a complete void-pointer
                # argument, read against the prototypes of this file and its headers; rule P:
                # the typed pointer's type and its binding
                admitted = {**whole_object_sites(joined, symbol, fragments), **typed_admitted}
                for offset, message in typed_findings:
                    finding(offset, message)
                for reference in references:
                    if reference.start() in admitted:
                        continue
                    if not re.match(r"\s*\.\s*[A-Za-z_]", joined[reference.end():]):
                        finding(reference.start(), f"allowlisted volatile {symbol} may only be "
                                "used as `symbol.member`: its address or whole object would "
                                "carry the qualifier to other memory")
                for offset, message in member_provenance(joined, entry, admitted):
                    finding(offset, message)
                for extension in re.finditer(r"\b__extension__\b", joined):
                    finding(extension.start(), f"`__extension__` may not appear in a {symbol} user: "
                            "it admits lvalue forms that reach a member's address")
                # Defence in depth for the provenance rules (match.py also
                # applies them to the preprocessed text): in a file that uses
                # the object, no macro may expand to `&` or to any identifier
                # of the pinned declaration.
                for directive in directives:
                    if directive["kind"] == "define" and user_macro(directive["rest"], names):
                        finding(directive.start(), f"a macro in a {symbol} user may not expand "
                                "to `&` or to a name of the pinned declaration")
                # ... nor may any header it includes (other than the listed one)
                for included in sorted(inside or ()):
                    if included in (relpath, header) or tree is None:
                        continue
                    try:
                        other = strip_comments_and_strings(join_splices(
                            (Path(tree) / included).read_text(encoding="utf-8", errors="replace")))
                    except OSError:
                        finding(0, f"cannot read {included}, which a {symbol} user includes")
                        continue
                    for directive in re.finditer(r"(?m)^[ \t]*#[ \t]*define[ \t]+[A-Za-z_]\w*([^\n]*)",
                                                 other):
                        if user_macro(directive[1], names):
                            finding(0, f"{included}, included by a {symbol} user, defines a macro "
                                    "that expands to `&` or to a name of the pinned declaration")
            continue
        if relpath != header:
            for reference in references:
                finding(reference.start(), f"{symbol} is declared volatile only in {header}; "
                        "other headers may not name it")
            continue
        references = list(re.finditer(r"\b" + re.escape(symbol) + r"\b", code))
        declarations = list(re.finditer(
            r"(?m)^[ \t]*extern\s+struct\s*\{(?P<body>[^{}]*)\}\s*" + re.escape(symbol) +
            r"\s*;", code))
        if len(declarations) != 1 or len(references) != 1 or \
                not declarations[0].start() <= references[0].start() < declarations[0].end() or \
                re.search(SPLICE, text if text is not None else code):
            for reference in references or [None]:
                finding(reference.start() if reference else 0,
                        f"{header} must declare {symbol} exactly once as a file-scope "
                        f"`extern struct {{ ... }} {symbol};` and name it nowhere else")
            continue
        body = declarations[0]
        if declaration_tokens(body[0]) != pinned:
            finding(body.start(), f"the {symbol} declaration differs from the one pinned in "
                    "tools/volatile_allow.json; only the maintainer may change it")
            continue
        if re.search(r"\b(?:struct|union|enum|typedef|extern|static)\b|[#()\[\]=]",
                     re.sub(r"\[\s*(?:0x[0-9A-Fa-f]+|[0-9]+)\s*\]", "", body["body"])):
            finding(body.start(), f"the {symbol} declaration may only hold plain members")
            continue
        # A listed type qualifies only a full-width bit-field of a type
        # whose width the kit knows (`volatile u8 x : 8`, `volatile u16 x :
        # 16`): the semantic check models exactly those members.
        types = "|".join(re.escape(t) for t in entry["member_types"] if t in BIT_FIELD_WIDTHS)
        member = re.compile(r"volatile\s+(?P<type>" + (types or r"(?!)") + r")\s+[A-Za-z_]\w*"
                            r"\s*:\s*(?P<width>[0-9]+)\s*;")
        for qualifier in re.finditer(r"\bvolatile\b", body["body"]):
            offset = body.start("body") + qualifier.start()
            prefix = code[body.start("body"):offset]
            found = member.match(code, offset)
            if re.search(r"(?:^|;)\s*$", prefix) and found and \
                    integer_literal(found["width"]) == BIT_FIELD_WIDTHS[found["type"]]:
                allowed.add(offset)
    return allowed, findings


BIT_FIELD_WIDTHS = {"u8": 8, "s8": 8, "u16": 16, "s16": 16}
C_TOKEN = re.compile(r"[A-Za-z_]\w*|0[xX][0-9A-Fa-f]+[uUlL]*|[0-9]+[uUlL]*|->|\+\+|--|<<=|>>=|<<|>>|"
                     r"<=|>=|==|!=|&&|\|\||[-+*/%&|^]=|\S")
def integer_literal(token):
    """the value of a plain decimal, octal or hex literal, else None"""
    if re.fullmatch(r"0[xX][0-9A-Fa-f]+", token):
        return int(token, 16)
    if re.fullmatch(r"0[0-7]*", token):
        return int(token, 8)
    if re.fullmatch(r"[1-9][0-9]*", token):
        return int(token)
    return None


# kit#375, rule U: the allowlisted object's whole-object argument.  A `void *` or
# `const void *` parameter (any order of the qualifier, an optional name).
VOID_POINTER_PARAMETER = re.compile(
    r"(?:(?:const|__const|__const__)\s+)?void\s*(?:(?:const|__const|__const__)\s*)?\*"
    r"\s*(?:[A-Za-z_]\w*)?")
NOT_CALLEES = {"if", "while", "for", "switch", "return", "sizeof", "typeof", "__typeof", "__typeof__",
               "__alignof__", "__alignof", "__attribute__", "__extension__", "do", "else", "case"}


def declaration_fragments(code):
    """the file-scope declarations of code split at `;`, with directive lines and
    brace bodies folded to `;`, or None when the braces do not balance"""
    text = re.sub(r"(?m)^[ \t]*#.*$", ";", code)
    while True:
        folded = re.sub(r"\{[^{}]*\}", ";", text)
        if folded == text:
            return None if "{" in text or "}" in text else text.split(";")
        text = folded


def parameter_list(text):
    """the top-level comma-separated parts of a parameter list, or None"""
    parts, depth, start = [], 0, 0
    for index, char in enumerate(text):
        depth += {"(": 1, ")": -1, "[": 1, "]": -1}.get(char, 0)
        if depth < 0:
            return None
        if char == "," and depth == 0:
            parts.append(text[start:index])
            start = index + 1
    if depth:
        return None
    parts.append(text[start:])
    return [part.strip() for part in parts]


def void_pointer_indices(parameters):
    """the indices of the `void *` / `const void *` parameters of a list, or None"""
    parts = parameter_list(parameters)
    if parts is None or parts == ["void"] or "..." in parts:
        return None
    return frozenset(i for i, part in enumerate(parts) if VOID_POINTER_PARAMETER.fullmatch(part))


def void_pointer_parameters(fragments, callee):
    """the parameter indices that every file-scope prototype of the function `callee`
    declares `void *` or `const void *`; empty unless every declaration of it is a
    plain prototype and all agree (kit#375, rule U)"""
    found = set()
    for fragment in fragments or ():
        named = re.search(r"\b" + re.escape(callee) + r"\b", fragment)
        if not named:
            continue
        text = " ".join(fragment.split())
        prototype = re.fullmatch(r"((?:[A-Za-z_]\w*\s*|\*\s*)+?)" + re.escape(callee) + r"\s*\((.*)\)", text)
        if prototype is None or re.search(r"\btypedef\b", prototype[1]):
            return frozenset()
        indices = void_pointer_indices(prototype[2])
        if indices is None:
            return frozenset()
        found.add(indices)
    return found.pop() if len(found) == 1 else frozenset()


def table_void_pointer_parameters(fragments, table):
    """the same for a call through an element of the function-pointer table `table`:
    `[extern] [const] T [const] table[N]` with one `typedef R (*T)(params)`, or a
    direct `R (*table[N])(params)` declarator; empty for anything else"""
    found = set()
    for fragment in fragments or ():
        if not re.search(r"\b" + re.escape(table) + r"\b", fragment):
            continue
        text = " ".join(fragment.split())
        typed = re.fullmatch(r"(?:(?:extern|const|static) )*([A-Za-z_]\w*) (?:const )?" + re.escape(table) +
                             r" ?(?:\[[^\]]*\])?", text)
        direct = re.fullmatch(r"(?:extern |const |static )*[A-Za-z_][\w ]*?\*? ?\( ?\* ?(?:const )?" +
                              re.escape(table) + r" ?(?:\[[^\]]*\])? ?\) ?\((.*)\)", text)
        if direct:
            indices = void_pointer_indices(direct[1])
        elif typed:
            definitions = [" ".join(f.split()) for f in fragments
                           if re.search(r"\btypedef\b", f) and re.search(r"\(\s*\*\s*" + re.escape(typed[1]) +
                                                                       r"\s*\)", f)]
            matched = [re.fullmatch(r"typedef [A-Za-z_][\w ]*?\*? ?\( ?\* ?" + re.escape(typed[1]) +
                                    r" ?\) ?\((.*)\)", d) for d in definitions]
            if len(matched) != 1 or matched[0] is None:
                return frozenset()
            indices = void_pointer_indices(matched[0][1])
        else:
            return frozenset()
        if indices is None:
            return frozenset()
        found.add(indices)
    return found.pop() if len(found) == 1 else frozenset()


def whole_object_sites(code, symbol, fragments):
    """{offset of the symbol's token: what it is} for the whole-object uses kit#375's
    rule U admits: `sizeof symbol` and `sizeof(symbol)`, and `&symbol`, cast or not to
    `(void *)` / `(const void *)`, as one complete top-level argument of a call to a
    prototyped function, or through an element `table[K]` of a typed function-pointer
    table, at a parameter declared `void *` or `const void *`, no other argument of
    that call naming the symbol.  Every other whole-object use stays refused."""
    tokens = [(m[0], m.start()) for m in C_TOKEN.finditer(code)]
    words = [token for token, _ in tokens]
    sites = {}
    for k, (token, offset) in enumerate(tokens):
        if token != symbol:
            continue
        if k >= 1 and words[k - 1] == "sizeof" or \
                k >= 2 and words[k - 2:k] == ["sizeof", "("] and words[k + 1:k + 2] == [")"]:
            sites[offset] = "sizeof"
            continue
        if k < 1 or words[k - 1] != "&" or words[k + 1:k + 2] not in ([","], [")"]):
            continue
        j = k - 2
        for cast in (["(", "void", "*", ")"], ["(", "const", "void", "*", ")"],
                     ["(", "void", "const", "*", ")"]):
            if j - len(cast) + 1 >= 0 and words[j - len(cast) + 1:j + 1] == cast:
                j -= len(cast)
                break
        located = void_pointer_argument(words, j, fragments)
        if located is None:
            continue
        name, index, p, q = located
        def sized(i):
            return words[i - 1] == "sizeof" or words[i - 2:i] == ["sizeof", "("] and words[i + 1:i + 2] == [")"]
        # the symbol may occur only here among the call's arguments
        if sum(words[i] == symbol and not sized(i) for i in range(p, q)) != 1:
            continue
        sites[offset] = f"the void-pointer argument {index + 1} of {name}"
    return sites


def void_pointer_argument(words, j, fragments):
    """(callee, argument index, its `(`, its `)`) when the argument after words[j] (a `(` or a `,`)
    is one at a `void *` / `const void *` parameter of a prototyped callee or of an element
    `table[K]` of a typed function-pointer table (kit#375, rule U), else None"""
    if j < 0 or words[j] not in ("(", ","):
        return None
    # back to the call's own `(`, counting the arguments before this one
    index, depth, p = (1 if words[j] == "," else 0), 0, j - 1 if words[j] == "," else j
    while words[j] == "," and p >= 0:
        if words[p] in (";", "{", "}"):
            p = -1
            break
        if words[p] in (")", "]"):
            depth += 1
        elif words[p] in ("(", "["):
            if depth == 0:
                break
            depth -= 1
        elif words[p] == "," and depth == 0:
            index += 1
        p -= 1
    if p < 1 or words[p] != "(":
        return None
    # forward to its `)`
    depth, q = 0, p
    while q < len(words):
        depth += {"(": 1, ")": -1}.get(words[q], 0)
        if depth == 0:
            break
        q += 1
    if q >= len(words):
        return None
    callee = words[p - 1]
    if callee == "]" and p >= 5 and words[p - 3] == "[" and integer_literal(words[p - 2]) is not None and \
            re.fullmatch(r"[A-Za-z_]\w*", words[p - 4]) and words[p - 5] not in (".", "->"):
        name, allowed = f"{words[p - 4]}[{words[p - 2]}]", table_void_pointer_parameters(fragments, words[p - 4])
    elif re.fullmatch(r"[A-Za-z_]\w*", callee) and callee not in NOT_CALLEES and \
            words[p - 2:p - 1] not in (["."], ["->"]):
        name, allowed = callee, void_pointer_parameters(fragments, callee)
    else:
        return None
    return (name, index, p, q) if index in allowed else None


C_KEYWORDS = {"auto", "break", "case", "char", "const", "continue", "default", "do", "double", "else", "enum",
              "extern", "float", "for", "goto", "if", "int", "long", "register", "return", "short", "signed",
              "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned", "void", "volatile",
              "while", "inline", "asm"}


def typed_pointer_sites(code, symbol, entry_declaration, fragments):
    """kit#375, rule P: (admitted symbol references, admitted typeof offsets, findings) for
    one typed pointer to the object.

    Exactly one block-scope declaration `__typeof__(symbol) *name;` (any typeof
    spelling, first in its statement, inside a function body), bound exactly once
    to `&symbol`: in its initialiser `= &symbol`, or by one statement
    `name = &symbol;` after it.  Every other use of `name` must be `name->member`
    with a non-array member of the declaration, not under `&`, or one complete
    argument at a `void *` / `const void *` parameter of a prototyped callee or
    typed table element, no other argument of that call naming the symbol or
    `name`.  Any other use of `name` is a finding.  Without exactly that shape
    nothing is admitted, and the typeof and `&` rules refuse as before.
    """
    tokens = [(m[0], m.start()) for m in C_TOKEN.finditer(code)]
    words = [token for token, _ in tokens]
    depth, depths = 0, []
    for word in words:
        depths.append(depth)
        depth += {"{": 1, "}": -1}.get(word, 0)
    declarations = []
    for k, word in enumerate(words):
        if word not in TYPEOF_WORDS:
            continue
        shape = words[k + 1:k + 6]
        if shape[:4] != ["(", symbol, ")", "*"] or len(shape) < 5 or \
                not re.fullmatch(r"[A-Za-z_]\w*", shape[4]) or shape[4] in C_KEYWORDS | TYPEOF_WORDS or \
                k == 0 or words[k - 1] not in ("{", ";", "}") or depths[k] < 1:
            return {}, set(), []
        declarations.append(k)
    if len(declarations) != 1:
        return {}, set(), []
    k = declarations[0]
    name = words[k + 5]
    admitted = {tokens[k + 2][1]: "the typed pointer's type"}
    bindings = []
    if words[k + 6:k + 10] == ["=", "&", symbol, ";"]:
        bindings.append(k + 8)
    elif words[k + 6:k + 7] != [";"]:
        return {}, set(), []
    arrays = set(re.findall(r"([A-Za-z_]\w*)\s*\[", entry_declaration))
    members = set(re.findall(r"([A-Za-z_]\w*)\s*(?:\[[^\]]*\]\s*)?(?::\s*\w+\s*)?;", entry_declaration)) - {symbol}
    uses = []
    for n, word in enumerate(words):
        if word != name or n == k + 5:
            continue
        if words[n + 1:n + 5] == ["=", "&", symbol, ";"] and words[n - 1] in ("{", ";", "}", ":") and n > k:
            bindings.append(n + 3)
            continue
        uses.append(n)
    if len(bindings) != 1:
        return {}, set(), []
    admitted[tokens[bindings[0]][1]] = "the typed pointer's binding"
    findings = []
    # the binding dominates every use: it is the initialiser, or a statement of the declaration's own
    # block (never below it in between), before every use, with no label after the declaration in that
    # block and no goto in the unit, so no path reaches a use without passing the binding
    binding = bindings[0]
    if binding != k + 8 and (depths[binding] != depths[k] or min(depths[k:binding + 1]) < depths[k]):
        findings.append((tokens[binding][1], f"the typed pointer `{name}` must be bound in its declaration's own "
                         "block, not in a nested or another block"))
    end = next((j for j in range(k + 1, len(words)) if depths[j] < depths[k]), len(words))
    for j in range(k + 1, end):
        label = words[j] in ("case", "default") or words[j + 1:j + 2] == [":"] and \
            re.fullmatch(r"[A-Za-z_]\w*", words[j]) and words[j - 1] in ("{", ";", "}")
        if label:
            findings.append((tokens[j][1], f"a label after the typed pointer `{name}`'s declaration could let a "
                             "path skip its binding"))
    for j, word in enumerate(words):
        if word == "goto":
            findings.append((tokens[j][1], f"`goto` in a unit with the typed pointer `{name}` could skip its "
                             "binding"))
    for n in [n for n in uses if n < binding]:
        findings.append((tokens[n][1], f"the typed pointer `{name}` is used before its binding"))
    uses = [n for n in uses if n > binding]
    for n in uses:
        before = n - 1
        while before >= 0 and words[before] == "(":
            before -= 1
        member = words[n + 2] if words[n + 1:n + 2] == ["->"] and len(words) > n + 2 else None
        if n > k and member in members and member not in arrays and words[n + 3:n + 4] != ["["] and \
                not (before >= 0 and words[before] == "&"):
            continue
        located = void_pointer_argument(words, n - 1, fragments) if n > k and words[n + 1:n + 2] in \
            ([","], [")"]) else None
        if located is not None:
            _, _, p, q = located
            def sized(i):
                return words[i - 1] == "sizeof" or words[i - 2:i] == ["sizeof", "("] and words[i + 1:i + 2] == [")"]
            if sum(words[i] in (symbol, name) and not (words[i] == symbol and sized(i)) for i in range(p, q)) == 1:
                continue
        findings.append((tokens[n][1], f"the typed pointer `{name}` to allowlisted volatile {symbol} may only "
                         f"be used as `{name}->member` or as a whole-object void-pointer argument"))
    return admitted, {tokens[k][1]}, findings


ASSIGNMENTS = {"=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "++", "--"}


def typed_copy_sites(code, symbol, entry_declaration):
    """kit#375, rule T: (admitted symbol references, admitted typeof offsets, findings) for
    one typed copy of the object in a struct member.

    Exactly one member declaration `__typeof__(symbol) name;` (any typeof
    spelling), first in its declaration, directly inside a `struct { ... }`
    body.  Every later `->name` or `.name` must be one of:
    - the save `E->name = symbol;`, a whole statement (no other assignment
      in it), which agbcc compiles to its memcpy;
    - the restore `symbol = E->name;`;
    - a member read `E->name.member` of a non-array member of the
      declaration: not assigned, incremented, indexed or called, and with no
      `&`, `++` or `--` earlier in its statement.
    Any other use of `name` is a finding.  Without exactly that declaration
    nothing is admitted, and the typeof and whole-object rules refuse as
    before.  The semantic check then ties the copy to the compiler's bound
    memcpy and follows its members through the permuted compile.
    """
    tokens = [(m[0], m.start()) for m in C_TOKEN.finditer(code)]
    words = [token for token, _ in tokens]
    openers, enclosing = [], []
    for k, word in enumerate(words):
        enclosing.append(openers[-1] if openers else None)
        if word == "{":
            openers.append(k)
        elif word == "}" and openers:
            openers.pop()
    declarations = []
    for k, word in enumerate(words):
        if word not in TYPEOF_WORDS:
            continue
        brace = enclosing[k]
        struct_body = brace is not None and (words[brace - 1:brace] == ["struct"] or
                                             words[brace - 2:brace - 1] == ["struct"] and
                                             re.fullmatch(r"[A-Za-z_]\w*", words[brace - 1]))
        shape = words[k + 1:k + 6]
        if not struct_body or shape[:3] != ["(", symbol, ")"] or len(shape) < 5 or \
                not re.fullmatch(r"[A-Za-z_]\w*", shape[3]) or shape[3] in C_KEYWORDS | TYPEOF_WORDS or \
                shape[4] != ";" or words[k - 1] not in ("{", ";"):
            return {}, set(), []
        declarations.append(k)
    if len(declarations) != 1:
        return {}, set(), []
    k = declarations[0]
    name = words[k + 4]
    local_findings = typed_copy_locals(words, tokens, enclosing[k], symbol)
    arrays = set(re.findall(r"([A-Za-z_]\w*)\s*\[", entry_declaration))
    members = set(re.findall(r"([A-Za-z_]\w*)\s*(?:\[[^\]]*\]\s*)?(?::\s*\w+\s*)?;", entry_declaration)) - {symbol}
    admitted, findings = {tokens[k + 2][1]: "the typed copy's type"}, []
    for n, word in enumerate(words):
        if word != name or n == k + 4:
            continue
        start = n - 1
        while start >= 0 and words[start] not in (";", "{", "}", ":"):
            start -= 1
        statement = words[start + 1:n]
        if n > k and words[n - 1] in ("->", "."):
            if words[n + 1:n + 4] == ["=", symbol, ";"] and not set(statement) & (ASSIGNMENTS | {"return", "?", ","}):
                admitted[tokens[n + 2][1]] = "the typed copy's save"
                continue
            if words[n + 1:n + 2] == [";"] and statement[:2] == [symbol, "="] and \
                    not set(statement[2:]) & (ASSIGNMENTS | {"return", "?", ","}):
                admitted[tokens[start + 1][1]] = "the typed copy's restore"
                continue
            if words[n + 1:n + 2] == ["."] and len(words) > n + 2 and words[n + 2] in members and \
                    words[n + 2] not in arrays and words[n + 3:n + 4] not in [[op] for op in ASSIGNMENTS] + \
                    [["["], ["("]] and not set(statement) & {"&", "++", "--"}:
                continue
        findings.append((tokens[n][1], f"the typed copy `{name}` of allowlisted volatile {symbol} may only be "
                         f"saved from it, restored to it, or read by member"))
    return admitted, {tokens[k][1]}, findings + local_findings


def typed_copy_locals(words, tokens, brace, symbol):
    """kit#375, rule T: findings for every instance of the struct holding the typed copy that is declared
    inside a function body (a local copy, frame or static), which the rule does not admit"""
    depth, close = 0, brace
    while close < len(words):
        depth += {"{": 1, "}": -1}.get(words[close], 0)
        if depth == 0:
            break
        close += 1
    names = set()
    if words[brace - 1:brace] == ["struct"] and words[brace - 2:brace - 1] == ["typedef"] or \
            words[brace - 3:brace - 2] == ["typedef"] and words[brace - 2:brace - 1] == ["struct"]:
        if close + 1 < len(words) and re.fullmatch(r"[A-Za-z_]\w*", words[close + 1]):
            names.add((words[close + 1],))
    if words[brace - 2:brace - 1] == ["struct"] and re.fullmatch(r"[A-Za-z_]\w*", words[brace - 1]):
        names.add(("struct", words[brace - 1]))
    # function bodies: a `{` after a `)` at file scope, to its `}`
    bodies, depth = [], 0
    for j, word in enumerate(words):
        if word == "{":
            if depth == 0 and j and words[j - 1] == ")":
                bodies.append([j, None])
            depth += 1
        elif word == "}":
            depth -= 1
            if depth == 0 and bodies and bodies[-1][1] is None:
                bodies[-1][1] = j
    findings = []
    for start, end in bodies:
        for j in range(start + 1, end or len(words)):
            for spelling in names:
                if words[j:j + len(spelling)] == list(spelling) and \
                        re.fullmatch(r"[A-Za-z_]\w*", words[j + len(spelling)] if j + len(spelling) < len(words) else ""):
                    findings.append((tokens[j][1], f"a local instance of the struct holding the typed copy of "
                                     f"{symbol} is not admitted: the copy must live outside the frame"))
    return findings


def user_macro(rest, names):
    """does a #define's parameters-and-replacement text expand to `&` or a pinned name?"""
    return "&" in rest or bool(set(re.findall(r"[A-Za-z_]\w*", macro_replacement(rest))) & names)


def macro_replacement(rest):
    """the replacement list of a #define, given the text after its name"""
    if rest.startswith("("):
        close = rest.find(")")
        return rest[close + 1:] if close >= 0 else ""
    return rest


def forges_directive(rest):
    """`#` in an object-like replacement.

    Such a macro can put a bare `#` at the start of a line and forge a
    linemarker or directive (`#define H #` then `H 1 "include/x.h"`).  In a
    function-like macro `#` must stringize a parameter, so it always yields
    a string literal, never a bare `#`.
    """
    return not rest.startswith("(") and "#" in rest


def whole_object_uses(code, symbol, admitted=()):
    """[(offset, message)] for every occurrence of symbol not written `symbol . member`.

    The one exception is the pinned declaration's own `} symbol ;`, which a
    preprocessed source contains exactly once.  This refuses whole-object
    sizeof, __alignof__, copies and address-taking on preprocessed text,
    where a macro can no longer hide them.
    """
    tokens = [(m[0], m.start()) for m in C_TOKEN.finditer(code)]
    findings, declarations = [], 0
    for index, (token, offset) in enumerate(tokens):
        if token != symbol or offset in admitted:
            continue
        after = [t for t, _ in tokens[index + 1:index + 3]]
        if after[:1] == ["."] and len(after) == 2 and re.fullmatch(r"[A-Za-z_]\w*", after[1]):
            continue
        if index and tokens[index - 1][0] == "}" and after[:1] == [";"] and not declarations:
            declarations += 1
            continue
        findings.append((offset, f"{symbol} may only be used as `{symbol}.member`: the whole object "
                         "(its size, alignment, address or a copy) depends on the pinned layout"))
    return findings


def member_provenance(code, entry, admitted=()):
    """[(offset, message)] for uses that could reach a volatile member without its name.

    Works on C tokens, so it applies equally to a source and to its
    preprocessed text.  An array member of the object may only be written
    `symbol.array[literal]` with the literal inside the array (no decay,
    pointer arithmetic, `k[array]` or `(symbol.array)[k]`).  No `&` may
    precede the symbol (through any `(`), unary or binary, so no member's
    address can be taken however it is spelt; write `symbol.x & a`.  Casts
    and type names that hold a struct or union body or an abstract `(*)`
    declarator are refused, since they can reinterpret the object.
    """
    symbol = entry["symbol"]
    arrays = {name: integer_literal(size) for name, size in re.findall(
        r"([A-Za-z_]\w*)\s*\[\s*(0[xX][0-9A-Fa-f]+|[0-9]+)\s*\]", entry["declaration"])}
    tokens = [(m[0], m.start()) for m in C_TOKEN.finditer(code)]
    findings = []
    # `&( ... symbol ... )`: a parenthesised operand of `&` holding the symbol
    # (a comma or conditional lvalue) takes a member's address.
    for index, (token, offset) in enumerate(tokens[:-1]):
        if token != "&" or tokens[index + 1][0] != "(":
            continue
        depth, close = 0, index + 1
        while close < len(tokens):
            depth += {"(": 1, ")": -1}.get(tokens[close][0], 0)
            if depth == 0:
                break
            close += 1
        if any(t == symbol for t, _ in tokens[index + 2:close]):
            findings.append((offset, f"`&(...)` around {symbol} may not take a member's address"))
    # every qualifier and signedness spelling gcc/c-parse.gperf reserves
    qualifiers = {"const", "__const", "__const__", *VOLATILE_SPELLINGS, "restrict", "__restrict",
                  "__restrict__", "__extension__", "signed", "__signed", "__signed__", "unsigned"}
    for index, (token, offset) in enumerate(tokens):
        if token != "(":
            continue
        after = index + 1
        while after < len(tokens) and tokens[after][0] in qualifiers:
            after += 1
        rest = [t for t, _ in tokens[after:after + 3]]
        if rest[:1] in (["struct"], ["union"]):
            # a body anywhere before the type name's `)`: after a tag or
            # attributes (`struct __attribute__((packed)) { ... }`) too
            depth, probe = 0, after + 1
            while probe < len(tokens) and depth >= 0 and tokens[probe][0] != "{":
                depth += {"(": 1, ")": -1}.get(tokens[probe][0], 0)
                probe += 1
            if depth >= 0 and probe < len(tokens) and tokens[probe][0] == "{":
                findings.append((offset, f"a type name with a struct or union body may not appear in a "
                                 f"{symbol} user: it can reinterpret the object"))
        if rest[:1] == ["*"]:
            close = after + 1
            while close < len(tokens) and (tokens[close][0] in qualifiers or tokens[close][0] == "*"):
                close += 1
            if close < len(tokens) and tokens[close][0] == ")":
                findings.append((offset, f"an abstract `(*)` declarator may not appear in a {symbol} "
                                 "user: it can reinterpret the object"))
    for index, (token, offset) in enumerate(tokens):
        if token != symbol:
            continue
        before = index - 1
        while before >= 0 and tokens[before][0] == "(":
            before -= 1
        if before >= 0 and tokens[before][0] == "&" and offset not in admitted:
            findings.append((offset, f"no `&` may precede {symbol} (write `{symbol}.x & a`): "
                             "a member's address could reach a volatile member without its qualifier"))
        after = [t for t, _ in tokens[index + 1:index + 6]]
        if after[:1] != ["."] or len(after) < 2 or after[1] not in arrays:
            continue
        member = after[1]
        value = integer_literal(after[3]) if len(after) >= 5 and after[2] == "[" and after[4] == "]" \
            else None
        if value is None or value >= arrays[member]:
            findings.append((offset, f"`{symbol}.{member}` may only be used as `{symbol}.{member}"
                             f"[literal]` with a literal below {arrays[member]}: anything else could "
                             "reach a volatile member without its qualifier"))
    return findings


def strip_comments_and_strings_keep_strings(text):
    """comments blanked, string and character literals kept (for #include)"""
    code = strip_comments_and_strings(text)
    out = list(code)
    for literal in re.finditer(r'"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\'', text):
        if code[literal.start()] == " " and not code[literal.start():literal.end()].strip():
            out[literal.start():literal.end()] = text[literal.start():literal.end()]
    return "".join(out)


def include_closure(root, source):
    """(root-relative paths a source can #include transitively, escapes).

    Escapes are included files that are neither under include/ nor a header
    under src/, so the plausibility sweep never lints them.

    Quoted names resolve against the including file's directory, then
    include/; angled names against include/ only (the tools run cpp with
    -nostdinc -I include).  Computed includes are refused while an entry is
    active, so this over-approximates the preprocessor's dependencies.
    """
    root = Path(root).resolve()
    start = Path(source).resolve()
    seen, pending, outside = set(), [start], []
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        text = strip_comments_and_strings_keep_strings(join_splices(
            path.read_text(encoding="utf-8", errors="replace")))
        for include in re.finditer(r'(?m)^[ \t]*#[ \t]*include[ \t]*(?:"([^"\n]+)"|<([^>\n]+)>)', text):
            name = include[1] or include[2]
            candidates = ([path.parent / name] if include[1] else []) + [root / "include" / name]
            for candidate in candidates:
                if candidate.is_file():
                    resolved = candidate.resolve()
                    if not ((root / "include") in resolved.parents or
                            (root / "src") in resolved.parents and resolved.suffix == ".h"):
                        outside.append(name)
                    pending.append(resolved)
                    break
    return ({path.relative_to(root).as_posix() for path in seen if root in path.parents},
            sorted(set(outside)))


def allowlisted_volatile_used(root, address, entries=None):
    """the active allow-list entries whose object the addressed source uses.

    A use is the source reaching the listed header through its include
    closure, or naming the symbol without declaring it itself.
    """
    root = Path(root)
    try:
        data_symbols = json.loads((root / "config" / "data_symbols.json").read_text())
    except (OSError, ValueError):
        data_symbols = {}
    if not isinstance(data_symbols, dict):
        data_symbols = {}
    entries = volatile_allow_entries() if entries is None else entries
    sources = sorted((root / "src").rglob(f"{address:08X}.c"))
    used = []
    for entry in active_volatile_entries(data_symbols, entries):
        symbol = re.escape(entry["symbol"])
        for source in sources:
            code = strip_comments_and_strings(join_splices(
                source.read_text(encoding="utf-8", errors="replace")))
            if entry["header"] in include_closure(root, source)[0] or \
                    re.search(r"\b" + symbol + r"\b", code) and not declares_symbol(code, entry["symbol"]):
                used.append(entry)
                break
    return used


def allowlisted_volatile_uses(root, address, entries=None):
    """report records for allowlisted volatile objects the addressed source uses.

    Each record binds the header's current SHA-256; an unreadable header
    raises OSError, which callers treat as a failure.  match.py adds the
    semantic-check record (allowlisted_volatile_semantics) after these.
    """
    records = []
    for entry in allowlisted_volatile_used(root, address, entries):
        digest = hashlib.sha256((Path(root) / entry["header"]).read_bytes()).hexdigest()
        records.append(f"* allowlisted volatile: `{entry['symbol']}` at "
                       f"`{entry['address']}` declared in `{entry['header']}` "
                       f"(SHA-256 `{digest}`)")
    if address == 0x08000718:
        import boot_dma0_shadow as dma
        records.append(dma.record(root))
    if address == 0x081457FC:
        import m4a_dma_counter
        records.append(m4a_dma_counter.record(root))
    if address == 0x080D9C58:
        import window_task
        records.append(window_task.record(root))
    if address in (0x080D9F60, 0x080DA074, 0x080DA968, 0x080DA1C4, 0x080DA3B8, 0x080DA598, 0x0811435C):
        import window_scanline
        if window_scanline.uses_element(root, address):
            records.append(window_scanline.record(root, address))
    if address == 0x08000FC8:
        import affine_oam_slot
        records.append(affine_oam_slot.record(root))
    if address == 0x0804BF78:
        import tile_cpufill32
        records.append(tile_cpufill32.record(root))
    if address == 0x081418C0:
        import flash_read_id
        records.append(flash_read_id.record(root))
    if address == 0x08141EB8:
        import flash_chip_erase
        records.append(flash_chip_erase.record(root))
    if address == 0x08141F2C:
        import flash_sector_erase
        records.append(flash_sector_erase.record(root))
    if address == 0x08141FC8:
        import flash_program_byte
        records.append(flash_program_byte.record(root))
    if address == 0x0814189C:
        import flash_bank_command
        records.append(flash_bank_command.record(root))
    if address == 0x0800DB0C:
        import blend_ramp
        records.append(blend_ramp.record(root))
    if address == 0x0800D3BC:
        import bg_affine_rows
        records.append(bg_affine_rows.record(root))
    if address == 0x0800DE70:
        import scanline_pair
        records.append(scanline_pair.record(root))
    if address == 0x0800C720:
        import scanline_wave
        records.append(scanline_wave.record(root))
    import bios_fill_temporary
    fill = bios_fill_temporary.record(root, address)
    if fill is not None:
        records.append(fill)
    import volatile_rom_proof
    proof = volatile_rom_proof.record(root, address)
    if proof is not None:
        records.append(proof)
    return records


def inert_control_flow(text, lines=None):
    """find `if (c) X; else X;` - identical arms, so the test means nothing.

    This is the shape that appeared in a rejected match: the branches store the
    same value, so the only effect is to make the compiler keep a frame it
    would otherwise drop.  Semantically it is `X;`, and nobody writes that.
    lines, when given, is the text the offsets index, comments and all, which
    numbers the lines (text may be its stripped code).
    """
    hits = []
    pat = re.compile(
        r"\bif\s*\((?P<cond>[^()]*)\)(?P<a>[^;{}]*?)\s*;?\s*else"
        r"\s*(?P<b>[^;{}]*?)\s*;")
    for m in pat.finditer(text):
        a = " ".join(m.group("a").split())
        b = " ".join(m.group("b").split())
        if a and a == b:
            line = (text if lines is None else lines).count("\n", 0, m.start()) + 1
            hits.append((line, "inert-control-flow", "suspect",
                         f"`if ({m.group('cond').strip()}) {a}; else {b};` - both "
                         f"arms do the same thing, so the test exists only to "
                         f"change the generated code"))
    return hits


def hardware_polling_bodies(code, hardware_qualifiers, text=None):
    """Empty while bodies may poll a documented, fixed volatile MMIO macro.

    Only one object-like direct-access definition and a nonzero constant mask
    qualify. Function bodies, RAM reads, calls and mutable aliases still fail.
    A file with a line splice anywhere in text, comments included, never does.
    """
    bodies = set()
    if re.search(SPLICE, text if text is not None else code):
        return bodies
    definitions = list(re.finditer(
        r"(?m)^[ \t]*#[ \t]*define[ \t]+(?P<name>[A-Za-z_]\w*)[ \t]+"
        r"\(\s*\*\s*\(\s*(?P<v>volatile)\s+(?:u8|u16|u32)\s*\*\s*\)"
        r"\s*0x[0-9a-fA-F]+[uUlL]*\s*\)[ \t]*$", code))
    for definition in definitions:
        name = re.escape(definition['name'])
        directives = list(re.finditer(
            r"(?m)^[ \t]*#[ \t]*(?:define|undef)[ \t]+" + name + r"\b", code))
        if definition.start('v') not in hardware_qualifiers or len(directives) != 1:
            continue
        masked = name + r"\s*&\s*(?P<mask>0x[0-9a-fA-F]+|[0-9]+)[uUlL]*"
        condition = r"(?:" + masked + r"|!\s*\(\s*" + masked.replace('?P<mask>', '?P<negated_mask>') + r"\s*\))"
        for loop in re.finditer(r"\bwhile\s*\(\s*" + condition +
                                r"\s*(?P<body>\)\s*\{\s*\})", code):
            mask = loop['mask'] or loop['negated_mask']
            if loop.start() > definition.end() and int(mask, 16 if mask.lower().startswith('0x') else 10):
                bodies.add(loop.start('body'))
    return bodies


def statement_macro_tails(code):
    """Offsets of `while (0)` closing complete, nonempty do-statement macros.

    Such a macro executes its body once. Only its closing condition is exempt;
    the body is still scanned for dead code and every other forbidden construct.
    Comments and literals have already been blanked without changing offsets.
    """
    logical = re.sub(SPLICE, lambda match: " " * len(match[0]), code)
    tails = set()
    headers = re.finditer(
        r"(?m)^[ \t]*#[ \t]*define[ \t]+[A-Za-z_]\w*(?:\([^()\r\n]*\))?", logical)
    for header in headers:
        end = logical.find("\n", header.end())
        if end < 0:
            end = len(logical)
        opener = re.match(r"\s*do\b\s*\{", logical[header.end():end])
        if opener is None:
            continue
        opening = header.end() + opener.end() - 1
        depth = 1
        closing = opening + 1
        while closing < end and depth:
            if logical[closing] == "{":
                depth += 1
            elif logical[closing] == "}":
                depth -= 1
            closing += 1
        if depth or not logical[opening + 1:closing - 1].strip(" \t\r\n;"):
            continue
        body = code[opening + 1:closing - 1]
        joined_body = join_splices(body)
        # Do not let a newly accepted wrapper conceal a forbidden token split
        # across physical lines; the ordinary rule scan retains source offsets.
        if any(re.search(pattern, joined_body) and not re.search(pattern, body)
               for _, _, pattern, _ in RULES) or \
                (inert_control_flow(joined_body) and not inert_control_flow(body)):
            continue
        tail = re.fullmatch(r"\s*(while\s*\(\s*0\s*\))\s*;?\s*", logical[closing:end])
        if tail is not None:
            tails.add(closing + tail.start(1))
    return tails


JOINED = " (with the file's line splices joined, as cpp reads it)"


def check_text(text, origin="", data_symbols=None, relpath=None, volatile_allow=None,
               closure=None, untranslated=None, tree=None, project=None):
    """returns list of findings: (line, rule, severity, message)

    relpath is the file's path relative to the project root; only the header
    an allowlisted volatile object names can be exempted, so None never is.
    closure is include_closure() of the file; without it no file is assumed
    unable to see an allowlisted declaration.

    cpp joins line splices before it reads a token, so a file with a splice
    is checked twice: as written, and with its splices joined (kit#357).  A
    finding of either view is a finding, so an exemption holds only where both
    views admit it, and a token split across a splice (`a\\<newline>sm`,
    `whi\\<newline>le (0)`) meets its rule.  A joined-view finding the written
    view does not also make on the same logical line is reported on that
    line's first physical line, marked JOINED.
    """
    findings = check_view(text, origin, data_symbols, relpath, volatile_allow, closure,
                          untranslated, tree, project)
    splice_lines = {text.count("\n", 0, match.start()) + 1 for match in re.finditer(SPLICE, text)}
    if not splice_lines:
        return findings
    first, logical, shift = {0: 0}, {0: 0}, 0
    for line in range(1, text.count("\n") + 2):
        logical[line] = line - shift
        first.setdefault(line - shift, line)
        shift += line in splice_lines
    seen = {}
    for line, rule, _, _ in findings:
        key = (logical.get(line, line), rule)
        seen[key] = seen.get(key, 0) + 1
    for line, rule, severity, message in check_view(join_splices(text), origin, data_symbols, relpath,
                                                    volatile_allow, closure, None, tree, project):
        if seen.get((line, rule), 0):
            seen[(line, rule)] -= 1
            continue
        findings.append((first.get(line, line), rule, severity, message + JOINED))
    findings.sort(key=lambda f: (f[0], f[1]))
    return findings


def exemptions(text, code, data_symbols=None, relpath=None, volatile_allow=None, closure=None,
               untranslated=None, tree=None, project=None, fill_temporaries=True):
    """(hardware, counter, allow-listed qualifier offsets, findings) of one view's exceptions.

    Every exception that admits a qualifier before the ROM proof is asked
    (volatile_rom_proof): the I/O window, the per-address modules, the VBlank
    DMA counter, the allow list and, last, the SDK's BIOS fill temporary
    (bios_fill_temporary, with the hardware offsets), which considers only
    what the others leave.  The proof considers only what none of them admits.
    """
    hardware_qualifiers = hardware_volatile_offsets(text, code, data_symbols or {})
    if relpath == "src/08000718.c" and tree is not None and project is not None and closure == (
            {relpath, "include/ffta.h"}, []):
        import boot_dma0_shadow as dma
        try:
            offsets, _ = dma.selected(text, tree, project, data_symbols or {})
            hardware_qualifiers.update(offsets)
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == "src/08145CAC.c" and tree is not None and closure == (
            {relpath, "include/ffta.h"}, []):
        import cgb_registers
        try:
            header = (Path(tree) / cgb_registers.HEADER).read_text(encoding="utf-8")
            source = strip_comments_and_strings_keep_strings(text)
            if cgb_registers.literal_defines(source, strip_comments_and_strings_keep_strings(header)):
                hardware_qualifiers.update(cgb_registers.selected_offsets(text, code))
        except (OSError, UnicodeError):
            pass
    if relpath == "src/0813FB7C.c" and tree is not None and project is not None and closure == (
            {relpath, "include/ffta.h"}, []):
        import sdk_cpuset_halfword
        try:
            offset = sdk_cpuset_halfword.selected_offset(text, tree, project)
            if offset is not None:
                hardware_qualifiers.add(offset)
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath in ("src/0811D4A0.c", "src/0811E034.c") and tree is not None and project is not None:
        import scene_scheduler_cpufill as scene_fill
        try:
            offset = scene_fill.qualifier(text, tree, project, int(relpath[4:-2], 16), closure)
            if offset is not None:
                hardware_qualifiers.add(offset)
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/080D9C58.c' and tree is not None and project is not None:
        import window_task
        try:
            hardware_qualifiers.update(window_task.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath in ('src/080D9F60.c', 'src/080DA074.c', 'src/080DA968.c', 'src/080DA1C4.c',
                   'src/080DA3B8.c', 'src/080DA598.c', 'src/0811435C.c') and tree is not None and project is not None:
        import window_scanline
        try:
            hardware_qualifiers.update(window_scanline.qualifier_offsets(
                text, tree, project, int(relpath[4:-2], 16), closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/08000FC8.c' and tree is not None and project is not None:
        import affine_oam_slot
        try:
            hardware_qualifiers.update(affine_oam_slot.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/0804BF78.c' and tree is not None and project is not None:
        import tile_cpufill32
        try:
            hardware_qualifiers.update(tile_cpufill32.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/081418C0.c' and tree is not None and project is not None:
        import flash_read_id
        try:
            hardware_qualifiers.update(flash_read_id.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/08141EB8.c' and tree is not None and project is not None:
        import flash_chip_erase
        try:
            hardware_qualifiers.update(flash_chip_erase.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/08141F2C.c' and tree is not None and project is not None:
        import flash_sector_erase
        try:
            hardware_qualifiers.update(flash_sector_erase.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/08141FC8.c' and tree is not None and project is not None:
        import flash_program_byte
        try:
            hardware_qualifiers.update(flash_program_byte.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/0814189C.c' and tree is not None and project is not None:
        import flash_bank_command
        try:
            hardware_qualifiers.update(flash_bank_command.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/0800DB0C.c' and tree is not None and project is not None:
        import blend_ramp
        try:
            hardware_qualifiers.update(blend_ramp.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/0800D3BC.c' and tree is not None and project is not None:
        import bg_affine_rows
        try:
            hardware_qualifiers.update(bg_affine_rows.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/0800DE70.c' and tree is not None and project is not None:
        import scanline_pair
        try:
            hardware_qualifiers.update(scanline_pair.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == 'src/0800C720.c' and tree is not None and project is not None:
        import scanline_wave
        try:
            hardware_qualifiers.update(scanline_wave.qualifier_offsets(text, tree, project, closure))
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    if relpath == "src/08003410.c" and tree is not None and project is not None:
        import boot_dma3_fill
        try:
            hardware_qualifiers.add(boot_dma3_fill.qualifier(text, tree, project, closure, data_symbols or {}))
        except (OSError, ValueError, KeyError, TypeError):
            pass
    if relpath in ("src/08000DBC.c", "src/08000E40.c") and project is not None:
        import immediate_dma_fill as dma_fill
        try:
            hardware_qualifiers.add(dma_fill.qualifier(text, tree, project, closure, int(relpath[4:-2], 16), data_symbols or {}))
        except (OSError, ValueError, KeyError, TypeError):
            pass
    counter_qualifiers = set()
    if relpath == "src/081457FC.c" and tree is not None and project is not None and closure == (
            {relpath, "include/ffta.h"}, []):
        import m4a_dma_counter as counter
        try:
            offset = counter.source_offset(text, (Path(tree) / counter.HEADER).read_bytes())
            if offset is not None:
                from rompath import rom_path
                rom = Path(rom_path(project)).read_bytes()
                counter.irq_evidence(rom)
                counter.owner_evidence(rom[counter.OWNER-counter.BASE:counter.OWNER-counter.BASE+56], True)
                counter_qualifiers.add(offset)
        except (OSError, ValueError, ImportError, SystemExit):
            pass
    listed_qualifiers, findings = allowlisted_volatile(
        code, relpath, data_symbols or {},
        volatile_allow_entries() if volatile_allow is None else volatile_allow, text, closure,
        untranslated, tree)
    if fill_temporaries and tree is not None and project is not None and VOLATILE_QUALIFIER.search(code):
        import bios_fill_temporary
        hardware_qualifiers |= bios_fill_temporary.qualifier_offsets(
            text, tree, project, relpath, hardware_qualifiers | counter_qualifiers | listed_qualifiers)
    return hardware_qualifiers, counter_qualifiers, listed_qualifiers, findings


def exempt_qualifiers(text, relpath, data_symbols, tree, project, closure, fill_temporaries=True):
    """the offsets of a source's qualifiers that an exception admits before the ROM proof (all but the
    BIOS fill temporary's when fill_temporaries is false)"""
    code = spell_digraphs(strip_comments_and_strings(text))
    hardware, counter, listed, _ = exemptions(text, code, data_symbols, relpath, None, closure, text,
                                              tree, project, fill_temporaries)
    return hardware | counter | listed


def data_symbols_of(root):
    """config/data_symbols.json of a tree, or {} when it is missing or malformed"""
    try:
        value = json.loads((Path(root) / "config" / "data_symbols.json").read_text())
    except (OSError, ValueError):
        return {}
    return value if isinstance(value, dict) else {}


def check_view(text, origin="", data_symbols=None, relpath=None, volatile_allow=None,
               closure=None, untranslated=None, tree=None, project=None):
    """check_text's findings for one view of a file: the text as given, splices and all.

    Every rule reads the code with its digraphs spelt as cpp reads them, so
    `%:if 0` meets the rule `#if 0` does (kit#408).
    """
    unspelt = strip_comments_and_strings(text)
    code = spell_digraphs(unspelt)
    macro_tails = statement_macro_tails(code)
    hardware_qualifiers, counter_qualifiers, listed_qualifiers, findings = exemptions(
        text, code, data_symbols, relpath, volatile_allow, closure, untranslated, tree, project)
    proved_qualifiers = set()
    if tree is not None and project is not None and VOLATILE_QUALIFIER.search(code):
        import volatile_rom_proof
        proved_qualifiers = volatile_rom_proof.qualifier_offsets(
            text, tree, project, relpath, hardware_qualifiers | listed_qualifiers | counter_qualifiers,
            data_symbols or {})
    polling_bodies = hardware_polling_bodies(code, hardware_qualifiers, text)
    # line numbers are counted in text: code's offsets are text's, but a block
    # comment's newlines are blanked in it
    for nul in re.finditer("\0", text):
        findings.append((text.count("\n", 0, nul.start()) + 1, "nul-byte", "error",
                         "a NUL byte: cpp reads it as whitespace, even inside a line splice, where "
                         "these scans read a character, and no real source holds one"))
    for offset, name in preprocessor_probes(text):
        findings.append((text.count("\n", 0, offset) + 1, "preprocessor-probe", "error",
                         f"`{name}` asks the preprocessor about the files or the build: no gcc 2.95-era "
                         "source does, and it can tell the volatile census's copy from the tree"))
    literals = spell_digraphs(unspelt, strip_comments_and_strings_keep_strings(text))
    for rid, sev, pat, msg in RULES:
        for m in re.finditer(pat, literals if rid == "asm-include" else code):
            if rid == "volatile" and m.start() in (hardware_qualifiers | listed_qualifiers | counter_qualifiers |
                                                   proved_qualifiers):
                continue
            if rid == "dead-code" and m.start() in macro_tails:
                continue
            if rid == "empty-body" and m.start() in polling_bodies:
                continue
            line = text.count("\n", 0, m.start()) + 1
            if sev == "suspect" and justified(text, line):
                continue
            # an inline-asm-looking thing inside a comment is not code
            findings.append((line, rid, sev, GNU_VOLATILE.format(m[0]) if rid == "volatile" and
                             m[0] != "volatile" else msg))
    findings += inert_control_flow(code, text)
    # comments are where hackiness gets admitted, so scan them raw too, justifications included: one
    # that admits steering justifies nothing (comment_justification)
    for i, raw in enumerate(text.split("\n"), 1):
        for rid, sev, pat, msg in RULES:
            if rid == "hack-vocabulary" and re.search(pat, raw):
                findings.append((i, rid, sev, msg))
    findings.sort(key=lambda f: (f[0], f[1]))
    return findings


def check_file(path):
    try:
        with open(path, encoding="utf-8", errors="replace", newline="") as source:
            untranslated = source.read()
        text = untranslated.replace("\r\n", "\n").replace("\r", "\n")
    except OSError as e:
        return [(0, "unreadable", "error", str(e))]
    data_symbols = {}
    relpath = closure = tree = None
    for parent in Path(path).resolve().parents:
        mapping = parent / "config" / "data_symbols.json"
        if mapping.is_file():
            try:
                value = json.loads(mapping.read_text())
                if isinstance(value, dict):
                    data_symbols = value
            except (OSError, ValueError):
                pass
            parts = Path(path).resolve().relative_to(parent).parts
            # Replays lint byte copies of the project's sources captured under
            # build/<capture>/; the copy's own layout is the relative path.
            tree = parent
            if len(parts) > 2 and parts[0] == "build":
                relpath = Path(*parts[2:]).as_posix()
                tree = parent / "build" / parts[1]
            else:
                relpath = Path(*parts).as_posix()
            try:
                closure = include_closure(tree, path)
            except OSError:
                closure = None
            break
    return check_text(text, os.path.basename(path), data_symbols, relpath, closure=closure,
                      untranslated=untranslated, tree=tree, project=parent if tree is not None else None)


def squeezed(text):
    """(text without backslashes, whitespace and control characters, the offset in text of each kept one)"""
    kept = [(index, char) for index, char in enumerate(text)
            if not (char <= "\x20" or char in "\x7f\\")]
    return "".join(char for _, char in kept), [index for index, _ in kept]


# Queries cpp answers about the files and the build: every `__has_` operator
# (`__has_include`, `__has_include_next`, `__has_embed`, ...), `#embed` and
# `__TIMESTAMP__`.  They are looked for with backslashes and whitespace
# deleted, so neither a line splice nor a desynchronised comment or literal
# hides one, and `#embed` may have comments between `#` (or `%:`) and `embed`.
# This is defence in depth only: token pasting builds a query no scan of the
# text can see, and the volatile census's random markers are what keep a
# source from telling the census's copy from the tree.
PROBE = re.compile(r"__has_\w*|__TIMESTAMP__|(?:#|%:|\?\?=)(?:/\*.*?\*/)*embed", re.S)


def preprocessor_probes(text):
    """[(offset in text, spelling)] of every preprocessor query (PROBE)"""
    flat, offsets = squeezed(text)
    return [(offsets[match.start()], match[0] if match[0].startswith("__") else "#embed")
            for match in PROBE.finditer(flat)]


# ------------------------------------------------------------------ the volatile census
# The rules read source text, but agbcc reads what cpp makes of it.  Token
# pasting, a line splice, or text the lint reads as a comment or a literal
# (kit#129) can give that translation unit a qualifier no rule saw, and typeof
# copies a qualifier onto an object the source never qualifies.  The census
# checks where each qualifier came from; where an exempt one ends up is the
# exceptions' business (kit#357).
TYPEOF_SPELLINGS = ("typeof", "__typeof__", "__typeof")
CENSUS_WORD = re.compile(r"[A-Za-z0-9_$]+")
# bytes that can join two pieces of one token (backslash splices) or that only
# separate tokens; with them deleted, any qualifier cpp could lex from a file,
# and any paste operator, is a plain substring of it
CENSUS_SQUEEZE = re.compile(rb"[\x00-\x20\x7f\\]")
CENSUS_HINTS = (b"volatile", b"asm", b"##", b"%:", b"??=", b"??/")
ASM_SPELLINGS = ("asm", "__asm", "__asm__")
# cpp output's string and character literals (to the end of the line when
# unterminated, as cpp reads them) and its identifier-like words
CENSUS_TOKEN = re.compile(r'"(?:\\.|[^"\\\n])*"?' r"|'(?:\\.|[^'\\\n])*'?|[A-Za-z0-9_$]+")
# a literal that cpp closes on its own line; cpp only warns about one that it
# does not, and agbcc's cc1 reads that one on across the newline
CENSUS_LITERAL = re.compile(r'"(?:\\.|[^"\\\n])*"' r"|'(?:\\.|[^'\\\n])*'")
MARKER_LETTERS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
# match.py's preprocessor (match.DEFAULT_CPP), pinned here so that the lint
# need not import match.py, and with it every profile module, except on
# Windows; a test keeps the two equal.
CENSUS_CPP = "cpp"
# The preprocessor options of the census and of both compiles match.py runs
# for a report, match.compile_object and switch_placement.compile_object: one
# string, so an option added to a compile reaches the census too.
CPP_OPTIONS = "-nostdinc -undef -I include"


# the marker of a qualifier the hardware exception admits (kit#357): its own,
# so the census can check where cpp puts it
HARDWARE = "hardware"


def census_markers(forbidden, choice=None):
    """a fresh marker per spelling: a reserved identifier as long as the spelling, `__` and letters or digits.

    One more marker, under HARDWARE and as long as `volatile`, renames the
    qualifiers the hardware exception admits.  Drawn at random on every run,
    so no source can spell one, and redrawn until none occurs in any of the
    forbidden texts (every input, raw and squeezed, and the real unit) or in
    another marker.
    """
    import secrets
    choice = choice or secrets.choice
    while True:
        markers = {spelling: "__" + "".join(choice(MARKER_LETTERS) for _ in range(len(spelling) - 2))
                   for spelling in VOLATILE_SPELLINGS + (HARDWARE,)}
        values = list(markers.values())
        if all(a == b or a not in b for a in values for b in values) and \
                not any(value in text for value in values for text in forbidden):
            return markers


def census_marked(text, markers, exempt=frozenset()):
    """text with every qualifier of the lint's code view replaced by its marker.

    A qualifier at an offset in exempt (one the hardware exception admits) gets
    the HARDWARE marker instead.
    """
    code = strip_comments_and_strings(text)
    pieces, last = [], 0
    for match in VOLATILE_QUALIFIER.finditer(code):
        marker = markers[HARDWARE] if match.start() in exempt and HARDWARE in markers else markers[match[0]]
        pieces += [text[last:match.start()], marker]
        last = match.end()
    return "".join(pieces) + text[last:]


def census_findings(real, marked, markers, typed=frozenset()):
    """why the qualifiers of `real` are not the lint's, given cpp's output for the marked copy.

    Empty when the real unit holds no qualifier, or when (1) the marked unit
    holds none either, (2) no marker was pasted into a longer token, (3) the
    marked unit with each marker mapped back is the real unit, byte for byte,
    and (4) the unit holds no typeof, except the typed pointer kit#375's rule P
    admits: typed holds the offsets, in the unit's code view, of the typeof
    tokens it admits, and every typeof of the unit must be one of them.
    """
    words = CENSUS_WORD.findall(real)
    if not any(word in VOLATILE_SPELLINGS for word in words):
        return []
    findings = []
    marked_words = CENSUS_WORD.findall(marked)
    values = set(markers.values())
    unread = sorted({word for word in marked_words if word in VOLATILE_SPELLINGS})
    if unread:
        findings.append(f"the translation unit holds `{unread[0]}` where no linted file spells the "
                        "qualifier in code: token pasting, a line splice or text the lint reads as a "
                        "comment or literal made it")
    pasted = sorted({word for word in marked_words
                     if word not in values and any(marker in word for marker in values)})
    if pasted:
        findings.append("a qualifier is pasted into a longer token in the translation unit")
    restored = marked
    for spelling, marker in markers.items():
        restored = restored.replace(marker, spelling if spelling in VOLATILE_SPELLINGS else "volatile")
    if restored != real:
        findings.append("the translation unit changes when only its linted qualifiers are renamed: "
                        "it depends on more than the text of its linted files")
    if any(word in TYPEOF_SPELLINGS for word in words):
        spots = [m.start() for m in re.finditer(r"\b(?:typeof|__typeof__|__typeof)\b",
                                                 strip_comments_and_strings(real))]
        if not typed or sum(word in TYPEOF_SPELLINGS for word in words) != len(spots) or \
                any(spot not in typed for spot in spots):
            findings.append("typeof in a translation unit that holds a volatile qualifier: it can copy "
                            "the qualifier onto an object the source never qualifies")
    return findings


def census_placement(marked, markers, data_symbols):
    """why a qualifier the hardware exception admitted is not where it holds in the marked unit (kit#357)"""
    marker = markers.get(HARDWARE)
    if marker is None or marker not in marked:
        return []
    unit = marked.replace(marker, "volatile")
    code, view = spell_digraphs(strip_comments_and_strings(unit)), operand_view(unit)
    typedefs = {name for name, _ in typedef_declarations(code)}
    for match in re.finditer(re.escape(marker), marked):
        if exempt_shape_holds(code, match.start(), data_symbols, view, typedefs):
            continue
        window = code[max(0, match.start() - 256):match.start()]
        prefix = re.search(r"\*\s*\(\s*\Z", window)
        access = prefix and HARDWARE_DIRECT.match(code, match.start() - len(window) + prefix.start())
        if access and access_context(view, access.start(), typedefs) == "address":
            return ["a justified hardware register's address is taken in the translation unit: the hardware "
                    "exception admits a register's address only when it is converted at once to `void *` or "
                    "to an integer, since a pointer could reach memory outside the I/O window (this is "
                    "conservative)"]
        return ["a justified hardware qualifier is not in an access the hardware exception admits once the "
                "translation unit is preprocessed: a macro, a typedef or the code around it changed the access"]
    return []


def census_unit(source):
    """(tree, path of the source in it) for a source under a `src` directory, else None"""
    for parent in source.parents:
        if parent.name == "src":
            return parent.parent, source.relative_to(parent.parent).as_posix()
    return None


def census_inputs(tree, name):
    """every file the compile may read: the addressed source, src/**/*.h, include/**.

    A superset of match_evidence.source_paths, whose resolved files are the
    only dependencies match.py's verify_dependencies admits.
    """
    paths = set()
    for top in ("src", "include"):
        for directory, _, files in os.walk(tree / top):
            paths.update(Path(directory) / file for file in files
                         if top == "include" or file.lower().endswith(".h") or file.lower() == name)
    return paths


def lint_text(data):
    """a file's bytes as check_file reads them"""
    return data.decode("utf-8", errors="replace").replace("\r\n", "\n").replace("\r", "\n")


def census_run(command, root):
    """run a shell command from root as match.Runner runs it (through WSL on Windows)"""
    if platform.system() == "Windows":
        import match
        return match.Runner(match.DEFAULT_CC, root=str(root)).sh(command)
    # no timeout, as for the compile itself (a bounded run needs POSIX process groups)
    result = subprocess.run(command, shell=True, capture_output=True, text=True, cwd=root)
    if result.returncode != 0:
        raise RuntimeError((result.stderr or result.stdout or "command failed").strip())
    return result.stdout


def volatile_census(address, linted):
    """[(path, rule, message)] for the addressed source's translation unit.

    Runs cpp as match.py does on the addressed source and again on a copy of
    the files it reads, each rewritten by census_marked with fresh markers, and
    applies census_findings.  Every file the unit reads must be one this run
    lints, read under one name.  No candidate input may hold a preprocessor
    query (preprocessor_probes), as defence in depth: the markers are drawn
    at random, so a query that tells the copy from the tree cannot make the
    copy spell one.  An asm keyword anywhere in the unit's code (outside
    literals) is inline asm, however cpp made it; a literal that runs past
    the end of its line, which cc1 and cpp read differently, is refused.  Skipped when no candidate
    input could produce a qualifier or an asm keyword (no `volatile`, `asm` or
    paste operator in any of them, with splices and whitespace deleted); a
    census that cannot run is a finding.
    """
    name = f"{address:08X}.c".lower()
    linted = [Path(path).resolve() for path in linted]
    sources = sorted({path for path in linted if path.name.lower() == name})
    if not sources:
        return []
    if len(sources) != 1:
        return [(sources[0], "volatile-census", "the volatile census needs exactly one addressed source")]
    source = sources[0]
    unit = census_unit(source)
    if unit is None:
        return []
    tree, relative = unit
    forbidden, hinted, failed = [], False, None
    for path in sorted(census_inputs(tree, name) | set(linted)):
        try:
            data = path.read_bytes()
        except OSError as error:
            failed = failed or error
            continue
        text = data.decode("utf-8", errors="replace")
        forbidden += [text, squeezed(text)[0]]
        hinted = hinted or any(hint in CENSUS_SQUEEZE.sub(b"", data) for hint in CENSUS_HINTS)
        probes = preprocessor_probes(text)
        if probes:
            return [(source, "volatile-census", f"{path.name} holds `{probes[0][1]}`: a preprocessor "
                     "query could tell the volatile census's copy from the tree")]
    if failed is not None:
        return [(source, "volatile-census", f"the volatile census could not read an input: {failed}")]
    if not hinted:
        return []
    try:
        command = f"{CENSUS_CPP} {CPP_OPTIONS} {shlex.quote(relative)}"
        base = tree.resolve()
        (base / "build").mkdir(exist_ok=True)
        # inside the tree, like match.py's own workspaces, so a WSL runner reaches it too
        with tempfile.TemporaryDirectory(prefix="ffta_census_", dir=base / "build") as work:
            work = Path(work)
            census_run(f"{command} -o {shlex.quote(work.relative_to(base).as_posix() + '/real.i')}", base)
            real = (work / "real.i").read_bytes().decode("utf-8")
            tokens = CENSUS_TOKEN.findall(real)
            if any(token[0] in "\"'" and not CENSUS_LITERAL.fullmatch(token) for token in tokens):
                return [(source, "multiline-literal", "a string or character literal in the translation "
                         "unit runs past the end of its line: cpp ends it there, but agbcc reads on "
                         "into the next line, so the census cannot read the unit as agbcc does")]
            asm = sorted({token for token in tokens if token in ASM_SPELLINGS})
            if asm:
                return [(source, "inline-asm", f"the translation unit holds `{asm[0]}`: inline asm, "
                         "even where a line splice or token pasting hides it from the rules")]
            if not any(word in VOLATILE_SPELLINGS for word in CENSUS_WORD.findall(real)):
                return []
            names = set()
            for marker in re.finditer(r'(?m)^#[ \t]+[0-9]+[ \t]+"((?:\\.|[^"\\\n])*)"', real):
                if not (marker[1].startswith("<") and marker[1].endswith(">")):
                    names.add(os.path.normpath(re.sub(r"\\(.)", r"\1", marker[1])))
            if any(os.path.isabs(name) or name.split(os.sep)[0] == os.pardir for name in names):
                return [(source, "volatile-census", "the translation unit reads a file outside its tree")]
            reads = {name: (base / name).resolve() for name in names}
            unlinted = sorted(set(reads.values()) - set(linted))
            if unlinted:
                return [(source, "volatile-census", f"the translation unit reads {unlinted[0].name}, "
                         "which this run does not lint")]
            identities = {(path.stat().st_dev, path.stat().st_ino) for path in reads.values()}
            if len(identities) != len(reads):
                return [(source, "volatile-census", "the translation unit reads one file under two names")]
            markers = census_markers(forbidden + [real])
            try:
                data_symbols = json.loads((base / "config" / "data_symbols.json").read_text())
            except (OSError, ValueError):
                data_symbols = {}
            data_symbols = data_symbols if isinstance(data_symbols, dict) else {}
            copy = work / "copy"
            for top in ("src", "include"):
                for directory, _, _ in os.walk(base / top):
                    (copy / Path(directory).relative_to(base)).mkdir(parents=True, exist_ok=True)
            for name, path in reads.items():
                target = copy / name
                target.parent.mkdir(parents=True, exist_ok=True)
                lint = lint_text(path.read_bytes())
                exempt = hardware_volatile_offsets(lint, strip_comments_and_strings(lint), data_symbols)
                target.write_bytes(census_marked(lint, markers, exempt).encode("utf-8"))
            census_run(f"{command} -o ../marked.i", copy)
            marked = (work / "marked.i").read_bytes().decode("utf-8")
    except (OSError, ValueError, RuntimeError, ImportError, subprocess.SubprocessError) as error:
        return [(source, "volatile-census", f"the volatile census could not preprocess the source: {error}")]
    # kit#375, rules P and T: the typeof of the one typed pointer to, or typed copy of, an
    # allowlisted object, as it reaches the unit.  The shape is read for each listed entry
    # whether or not this tree maps it (an owner replay lints a copy without the data map):
    # it only confines the typeof, and the qualifier itself is admitted elsewhere or not at all.
    typed, view = set(), strip_comments_and_strings(real)
    allow = volatile_allow_entries()
    for entry in active_volatile_entries({item.get("symbol"): item.get("address") for item in allow
                                          if isinstance(item, dict)}, allow):
        _, offsets, problems = typed_pointer_sites(view, entry["symbol"], entry["declaration"],
                                                   declaration_fragments(view))
        if not offsets:
            _, offsets, problems = typed_copy_sites(view, entry["symbol"], entry["declaration"])
        if not problems:
            typed |= offsets
    return [(source, "volatile-census", message) for message in
            census_findings(real, marked, markers, frozenset(typed)) +
            census_placement(marked, markers, data_symbols)]


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
    linted = []
    for p in args.paths:
        files = sorted(
            str(q) for q in Path(p).rglob("*")
            if q.is_file() and q.suffix in (".c", ".h")) \
            if os.path.isdir(p) else [p]
        linted += files
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
    if args.addr:
        try:
            address = int(args.addr, 16)
        except ValueError:
            census = [(Path(args.addr), "volatile-census", "the volatile census needs a hexadecimal --addr")]
        else:
            census = volatile_census(address, linted)
        for path, rule, message in census:
            total += 1
            all_findings.append({"file": str(path), "line": 0, "rule": rule,
                                 "severity": "error", "message": message})
            if not args.json:
                print(f"{path}:\n  {path.name}:0: ERROR: {rule}\n      {message}")

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
