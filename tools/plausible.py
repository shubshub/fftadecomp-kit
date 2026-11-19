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

agbcc reads `volatile`, `__volatile__` and `__volatile` as the same qualifier
(kit#93).  The `volatile` rule refuses all three, and every exception above
accepts only the plain spelling; in a file with a line splice, an exception
holds only where it also holds with the splices joined.  Every asm keyword
spelling, a NUL byte and a preprocessor query (`__has_include`, `#embed`, ...)
are refused outright.  With --addr the addressed source's translation unit is
also checked after cpp (volatile_census): each qualifier the compiler will see
must be one this run read as a qualifier, in code, in a file it linted, and
the unit may hold no asm keyword.
"""

import argparse
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
    ("asm-include", "error", r'#\s*include\s+"[^"]*\.(s|S)"',
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


# A backslash, optional horizontal whitespace and a newline: GCC's cpp splices
# the lines even with the whitespace (it only warns), so every scan must too.
# cpp counts a NUL byte as that whitespace as well.
SPLICE = r"\\[ \t\f\v\0]*\r?\n"


def join_splices(text):
    """translation phase 2, as the preprocessor does it"""
    return re.sub(SPLICE, "", text)


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


def hardware_volatile_offsets(text, code, data_symbols):
    """Recognize documented, directly bound MMIO qualifiers, not local steering."""
    allowed = set()
    if not re.search(r"\bvolatile\b", code):
        return allowed
    comments = []
    tokens = r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|//[^\n]*|/\*[\s\S]*?\*/'
    for token in re.finditer(tokens, text):
        if token[0].startswith(("//", "/*")) and JUSTIFY in token[0]:
            comments.append(text.count("\n", 0, token.end()) + 1)

    def justified_io(offset, address):
        line = text.count("\n", 0, offset) + 1
        return 0x04000000 <= address < 0x04000400 and any(
            comment in (line, line - 1) for comment in comments)

    ctype = r"(?:struct\s+|union\s+)?[A-Za-z_]\w*(?:\s+[A-Za-z_]\w*)*"
    direct = (r"\*\s*\(\s*(?P<v>volatile)\s+" + ctype +
              r"\s*\*\s*\)\s*(?P<address>0x[0-9a-fA-F]+)[uUlL]*\b(?=\s*(?:[;=),]|$))")
    for match in re.finditer(direct, code):
        if justified_io(match.start("v"), int(match["address"], 16)):
            allowed.add(match.start("v"))

    bound = (r"\b(?P<v>volatile)\s+" + ctype +
             r"\s*\*\s*(?:const\s+)?(?P<local>[A-Za-z_]\w*)\s*=\s*"
             r"&\s*(?P<symbol>[A-Za-z_]\w*)\s*;")
    bindings = list(re.finditer(bound, code))
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
        def conditional_dereference(before):
            prefix = before.rstrip()
            if not prefix.endswith("*"):
                return False
            prefix = prefix[:-1].rstrip()
            if re.search(r"\belse$", prefix):
                return True
            if not prefix.endswith(")"):
                return False
            depth = 0
            for index in range(len(prefix) - 1, -1, -1):
                if prefix[index] == ")":
                    depth += 1
                elif prefix[index] == "(":
                    depth -= 1
                    if depth == 0:
                        return re.search(r"\bif\s*$", prefix[:index]) is not None
            return False

        def direct_access(ref):
            before, after = code[:ref.start()], code[ref.end():]
            if re.match(r"\s*->", after):
                return not re.search(r"&\s*$", before)
            return ((re.search(r"(?:^|[=(:,;{}!~?&|^<>+\-/%\[\]])\s*\*\s*$|\breturn\s+\*\s*$", before) is not None or
                     conditional_dereference(before)) and
                    re.search(r"&\s*\*\s*$", before) is None and
                    re.match(r"\s*(?:\[|\+\+|--|\+=|-=|->|\.)", after) is None)

        if any(ref.span() not in declarations and not direct_access(ref)
               for ref in local_uses):
            continue
        if justified_io(match.start("v"), address):
            allowed.add(match.start("v"))
    return allowed


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
    argument or a copy.  Only a file with its own file-scope declarator whose
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
        findings.append((code.count("\n", 0, min(offset, len(code))) + 1,
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
        for typeof in re.finditer(r"\b(?:typeof|__typeof|__typeof__)\b", joined):
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
                for reference in references:
                    if not re.match(r"\s*\.\s*[A-Za-z_]", joined[reference.end():]):
                        finding(reference.start(), f"allowlisted volatile {symbol} may only be "
                                "used as `symbol.member`: its address or whole object would "
                                "carry the qualifier to other memory")
                for offset, message in member_provenance(joined, entry):
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


def whole_object_uses(code, symbol):
    """[(offset, message)] for every occurrence of symbol not written `symbol . member`.

    The one exception is the pinned declaration's own `} symbol ;`, which a
    preprocessed source contains exactly once.  This refuses whole-object
    sizeof, __alignof__, copies and address-taking on preprocessed text,
    where a macro can no longer hide them.
    """
    tokens = [(m[0], m.start()) for m in C_TOKEN.finditer(code)]
    findings, declarations = [], 0
    for index, (token, offset) in enumerate(tokens):
        if token != symbol:
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


def member_provenance(code, entry):
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
        if before >= 0 and tokens[before][0] == "&":
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
    if address == 0x0800C720:
        import scanline_wave
        records.append(scanline_wave.record(root))
    return records


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


def check_text(text, origin="", data_symbols=None, relpath=None, volatile_allow=None,
               closure=None, untranslated=None, tree=None, project=None):
    """returns list of findings: (line, rule, severity, message)

    relpath is the file's path relative to the project root; only the header
    an allowlisted volatile object names can be exempted, so None never is.
    closure is include_closure() of the file; without it no file is assumed
    unable to see an allowlisted declaration.
    """
    code = strip_comments_and_strings(text)
    macro_tails = statement_macro_tails(code)
    hardware_qualifiers = hardware_volatile_offsets(text, code, data_symbols or {})
    splices = [match.span() for match in re.finditer(SPLICE, text)]
    if splices:
        # cpp joins line splices before it reads a token, so an exemption holds
        # only where it also holds in the joined text: a splice can hide a
        # retarget from these scans (`d\<newline>ma = &ram;`), or open a comment
        # only cpp sees (`/\<newline>*`) that turns a statement into a macro tail.
        def physical(offset):
            """the offset in text of the joined text's character at offset"""
            for start, end in splices:
                if start > offset:
                    break
                offset += end - start
            return offset
        joined_text = join_splices(text)
        joined = strip_comments_and_strings(joined_text)
        macro_tails &= {physical(offset) for offset in statement_macro_tails(joined)}
        hardware_qualifiers &= {physical(offset) for offset in
                                hardware_volatile_offsets(joined_text, joined, data_symbols or {})}
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
    polling_bodies = hardware_polling_bodies(code, hardware_qualifiers, text)
    for nul in re.finditer("\0", text):
        findings.append((code.count("\n", 0, nul.start()) + 1, "nul-byte", "error",
                         "a NUL byte: cpp reads it as whitespace, even inside a line splice, where "
                         "these scans read a character, and no real source holds one"))
    for offset, name in preprocessor_probes(text):
        findings.append((code.count("\n", 0, offset) + 1, "preprocessor-probe", "error",
                         f"`{name}` asks the preprocessor about the files or the build: no gcc 2.95-era "
                         "source does, and it can tell the volatile census's copy from the tree"))
    for rid, sev, pat, msg in RULES:
        for m in re.finditer(pat, code):
            if rid == "volatile" and m.start() in hardware_qualifiers | listed_qualifiers | counter_qualifiers:
                continue
            if rid == "dead-code" and m.start() in macro_tails:
                continue
            if rid == "empty-body" and m.start() in polling_bodies:
                continue
            line = code.count("\n", 0, m.start()) + 1
            if sev == "suspect" and justified(text, line):
                continue
            # an inline-asm-looking thing inside a comment is not code
            findings.append((line, rid, sev, GNU_VOLATILE.format(m[0]) if rid == "volatile" and
                             m[0] != "volatile" else msg))
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


def census_markers(forbidden, choice=None):
    """a fresh marker per spelling: a reserved identifier as long as the spelling, `__` and letters or digits.

    Drawn at random on every run, so no source can spell one, and redrawn until
    none occurs in any of the forbidden texts (every input, raw and squeezed,
    and the real unit) or in another marker.
    """
    import secrets
    choice = choice or secrets.choice
    while True:
        markers = {spelling: "__" + "".join(choice(MARKER_LETTERS) for _ in range(len(spelling) - 2))
                   for spelling in VOLATILE_SPELLINGS}
        values = list(markers.values())
        if all(a == b or a not in b for a in values for b in values) and \
                not any(value in text for value in values for text in forbidden):
            return markers


def census_marked(text, markers):
    """text with every qualifier of the lint's code view replaced by its marker"""
    code = strip_comments_and_strings(text)
    pieces, last = [], 0
    for match in VOLATILE_QUALIFIER.finditer(code):
        pieces += [text[last:match.start()], markers[match[0]]]
        last = match.end()
    return "".join(pieces) + text[last:]


def census_findings(real, marked, markers):
    """why the qualifiers of `real` are not the lint's, given cpp's output for the marked copy.

    Empty when the real unit holds no qualifier, or when (1) the marked unit
    holds none either, (2) no marker was pasted into a longer token, (3) the
    marked unit with each marker mapped back is the real unit, byte for byte,
    and (4) the unit holds no typeof.
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
        restored = restored.replace(marker, spelling)
    if restored != real:
        findings.append("the translation unit changes when only its linted qualifiers are renamed: "
                        "it depends on more than the text of its linted files")
    if any(word in TYPEOF_SPELLINGS for word in words):
        findings.append("typeof in a translation unit that holds a volatile qualifier: it can copy "
                        "the qualifier onto an object the source never qualifies")
    return findings


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
        command = f"{CENSUS_CPP} -nostdinc -undef -I include {shlex.quote(relative)}"
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
            copy = work / "copy"
            for top in ("src", "include"):
                for directory, _, _ in os.walk(base / top):
                    (copy / Path(directory).relative_to(base)).mkdir(parents=True, exist_ok=True)
            for name, path in reads.items():
                target = copy / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(census_marked(lint_text(path.read_bytes()), markers).encode("utf-8"))
            census_run(f"{command} -o ../marked.i", copy)
            marked = (work / "marked.i").read_bytes().decode("utf-8")
    except (OSError, ValueError, RuntimeError, ImportError, subprocess.SubprocessError) as error:
        return [(source, "volatile-census", f"the volatile census could not preprocess the source: {error}")]
    return [(source, "volatile-census", message) for message in census_findings(real, marked, markers)]


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
