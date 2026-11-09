"""Semantic check for allowlisted volatile objects (kit#90).

An allowlisted declaration (tools/volatile_allow.json) may qualify byte and
halfword bit-fields of one RAM object as volatile, because the ROM shows the
qualifier's effect: a dead `ldrb`/`ldrh` of the member before every
`strb`/`strh` to it.
That alone does not stop a source from using the qualifier to plant code: a
statement such as `(sym.x, 0);`, `if (sym.x) ;`, an unused local or
`sym.x |= 0;` emits loads under the qualifier that an ordinary declaration
would not.

So match.py compiles the source twice: as written ("real") and with
`volatile` removed from exactly the pinned declaration in the preprocessed
text ("stripped").  The two function bodies are then compared here.  A
textual diff is not enough: removing the qualifier also changes register
allocation and address arithmetic, and a chained `a = (b = v)` re-reads `b`.
The comparison is therefore value-level: both bodies are executed
symbolically along every path, and the check requires

1. the same observable behaviour on every path: the same stores to
   non-stack memory with the same values, in the same order, the same calls
   with the same arguments, the same branch conditions and, for a non-void
   function, the same return value.  Memory is modelled as ordinary memory
   for both compiles, so this says the qualifier changed nothing that the
   program computes.  When a stack address escapes (a call argument or a
   stored value), every local frame byte, with the stores applied in order,
   joins the behaviour (incoming-argument slots included).  Every callee
   needs a file-scope prototype with a fixed list of one-word arguments;
   no prototype, `()`, `...`, indirect calls and wider arguments fail
   closed.  No prototype is trusted to name every register the callee
   reads, so every call counts as reading r0-r3, unless the callee is an
   indexed Thumb function whose ROM code shows which of them it reads
   (RomInterfaces, transitively through its own calls, failing closed);
2. every access to the object to be `symbol + constant` inside it; variable
   offsets, out-of-object offsets, multi-register transfers and the
   object's address reaching a call argument or a stored value fail closed;
3. every load of the object in the real compile to be one of
   * a read-modify-write load: an unsigned load of a pinned member, at its
     offset and of its width (`ldrb` of a byte, `ldrh` of a halfword), whose
     destination is overwritten before any use, followed by its store of
     the same width to the same member with only constant materialisation
     (immediate moves and arithmetic on known constants) and copies or
     literal loads into the store's operand registers in between
     (read_modify_write_store);
   * a chained re-read for `a = (b = v)`: the forwarding store of the same
     width to the same member is the immediately preceding memory access
     and the value feeds, through copies only, the next store, a store to a
     pinned member of its width (chained_reread);
   * a counterpart of the stripped compile's loads of the object, matched
     in order with the same address and width;
4. every access overlapping a pinned member to be exactly that member: its
   offset and its width (Executor.check_address), and every such store to
   carry its own read-modify-write load, except a store of the member's
   all-ones value once the permuted compile has shown it follows its member
   (agbcc's combine folds that store's insertion to the constant and drops
   the load);
5. no store to write back the value just loaded from the same member (an
   `ldrb`/`strb` or `ldrh`/`strh` self-assignment, `sym.x = sym.x` or
   `sym.x |= 0`).

The real/stripped comparison cannot tell `(void)sym.x; *(sym.array + k) =
v;` from `sym.x = v;`: they compile identically.  Provenance is therefore
enforced by the compiler.  A third compile permutes the pinned bit-fields
among their own slots, keeping every other offset, the size and the
alignment (perturbed_declaration); members move only among members of the
identical declaration form, so bytes swap with bytes and halfwords with
halfwords.  perturbation_check requires every pinned access to follow the
permutation; anything computed another way has the same address in both
compiles and cannot.  A bit-field has no address, so only its name can reach
it.  The executor refuses any access that overlaps a pinned member without
being exactly that member.  compare() also refuses, on the preprocessed
text, every occurrence of the symbol that is not `symbol.member`
(plausible.whole_object_uses) and plausible.py's member rules; those token
rules are defence in depth.

A pinned offset can also reach a value through memory: a store through
the pinned member of a typed copy, read back at a fixed offset.  So values
read back from memory (Executor.derived) may not build an object address,
and a branch on them is always a decision, imposed alike on every compile.

A planted read therefore either vanishes from the stripped compile, so the
real compile has a load the rules cannot explain, or it stays, which shows
the qualifier did not produce it; then it is ordinary code that the stripped
compile emits too.  Anything the symbolic executor does not model - ARM
code, computed jumps, symbolic loops beyond the path bound, unknown
instructions - fails closed with a reason.

Known limits (false refusals, never false acceptance of a qualifier
effect): reading a pinned member twice where an ordinary declaration would
reuse the first value (`if (x) ...; if (x) ...`) is refused, as are loops
whose exit depends on unknown values, stripped compiles that legally reorder
accesses around a pinned one, and equivalent code that the expression
normaliser cannot prove equal.  For halfword members that includes a narrow
read (`(u8)sym.h`, `sym.h & 0xFF`), which the stripped compile narrows to an
`ldrb` of the low byte that the overlap rule refuses; a signed read
(`(s16)sym.h`), whose `lsl`/`asr` the normaliser does not equate with the
other compile's sign extension; and the mixed chain `sym.h = (sym.b = a)`,
whose zero-extended byte the normaliser does not equate with the stripped
compile's `lsl #24; lsr #24` (`sym.b = (sym.h = a)` passes).

Without the permuted compile, an alias store paired with a planted read
(`(void)sym.h; p[1] = 0x100;` with `p` derived from another member) has the
shape of a read-modify-write store and passes the real/stripped rules; the
permutation is its only guard (the lexical provenance rules are defence in
depth).
"""

import re

from plausible import declaration_tokens

MASK = 0xFFFFFFFF
SP = ("sp",)
MAX_PATHS = 256
MAX_STEPS = 20000
MAX_DECISIONS = 32
RUNTIME_ARITY = {"__divsi3": 2, "__udivsi3": 2, "__modsi3": 2, "__umodsi3": 2}
ARGUMENT_REGISTERS = ("r0", "r1", "r2", "r3")
PINNED_WIDTHS = (1, 2)      # volatile members the rules model: bytes and halfwords
TYPE_SIZES = {"u8": 1, "s8": 1, "char": 1, "vu8": 1, "vs8": 1,
              "u16": 2, "s16": 2, "short": 2, "vu16": 2, "vs16": 2,
              "u32": 4, "s32": 4, "int": 4, "long": 4, "vu32": 4, "vs32": 4,
              "bool8": 1, "bool32": 4}
REGISTER_ALIASES = {"sb": "r9", "sl": "r10", "fp": "r11", "ip": "r12"}
INVERSE = {"eq": "ne", "ne": "eq", "cs": "cc", "cc": "cs", "hs": "lo", "lo": "hs",
           "mi": "pl", "pl": "mi", "vs": "vc", "vc": "vs", "hi": "ls", "ls": "hi",
           "ge": "lt", "lt": "ge", "gt": "le", "le": "gt"}


class SemanticError(ValueError):
    """the real and stripped compiles differ in a way the rules do not permit"""


# ---------------------------------------------------------------- declaration

def members(declaration):
    """[(member tokens, name, offset, bytes, volatile)] and the object size.

    The allow list restricts the declaration to plain members `T name;`,
    `T name[N];`, `T *name;` and full-width bit-fields `volatile T name : W;`
    of known integer types; anything else fails closed.
    """
    tokens = declaration_tokens(declaration)
    if tokens[:3] != ["extern", "struct", "{"] or tokens[-3:-2] != ["}"] or tokens[-1] != ";":
        raise SemanticError("pinned declaration is not `extern struct { ... } symbol;`")
    body, split, current = tokens[3:-3], [], []
    for token in body:
        if token == ";":
            split.append(current)
            current = []
        else:
            current.append(token)
    if current:
        raise SemanticError("pinned declaration has an unterminated member")
    offset, align, layout = 0, 1, []
    for whole in split:
        qualified = whole[:1] == ["volatile"]
        member = whole[1:] if qualified else whole
        if not member or member[0] not in TYPE_SIZES:
            raise SemanticError(f"pinned declaration member `{' '.join(member)}` has an unknown type")
        size, rest = TYPE_SIZES[member[0]], member[1:]
        if rest[:1] == ["*"]:
            size, rest = 4, rest[1:]
        count, bit_field = 1, False
        if len(rest) in (3, 4) and rest[1] in ("[", ":"):
            try:
                number = int(rest[2], 0)
            except ValueError:
                raise SemanticError(f"pinned declaration member `{' '.join(member)}` has an "
                                    "unreadable size or width") from None
        if len(rest) == 4 and rest[1] == "[" and rest[3] == "]":
            count, rest = number, rest[:1]
        elif len(rest) == 3 and rest[1] == ":":
            if number != 8 * size:
                raise SemanticError("only full-width bit-fields can be modelled")
            rest, bit_field = rest[:1], True
        if len(rest) != 1 or not re.fullmatch(r"[A-Za-z_]\w*", rest[0]):
            raise SemanticError(f"pinned declaration member `{' '.join(member)}` is not plain")
        offset = (offset + size - 1) // size * size
        align = max(align, size)
        if qualified and (size not in PINNED_WIDTHS or not bit_field):
            raise SemanticError("only volatile byte and halfword bit-fields can be modelled")
        layout.append((whole, rest[0], offset, size * count, qualified))
        offset += size * count
    return layout, (offset + align - 1) // align * align


def object_layout(declaration):
    """(object size, {offset of each volatile member}) of the pinned declaration"""
    size, pinned = pinned_members(declaration)
    return size, set(pinned)


def pinned_members(declaration):
    """(object size, {offset of each volatile member: its width in bytes})"""
    layout, size = members(declaration)
    return size, {offset: width for _, _, offset, width, qualified in layout if qualified}


def perturbed_declaration(declaration):
    """(declaration, {pinned offset: new offset}, size) with the pinned names permuted.

    The pinned bit-fields are grouped by declaration form (the member's
    tokens with its name taken out, so `volatile u8 _ : 8` and `volatile u16
    _ : 16` are two classes), and within each class they swap places among
    their own slots: the names are rotated by half the class's number (a
    derangement, so every pinned member moves, and not in order).  Every
    other member, the object's size and its alignment stay exactly the same,
    so nothing a source can compute from the layout - another member's
    address, sizeof, __alignof__ - changes.  A bit-field has no address, so
    a pinned member can only be reached through its own name, which follows
    the permutation; an access computed any other way stays put, at a slot
    that now belongs to a different member of the same width.
    """
    # The self-check below models the layout in Python.  That is sound only
    # because a name moves only between members whose declarations are
    # token-for-token identical apart from the name, so the rewrite is a
    # renaming of identical declarators and cannot change any offset, the
    # size or the alignment agbcc assigns, whatever its layout rules are.
    layout, size = members(declaration)
    classes = {}
    for index, (tokens, name, _, _, qualified) in enumerate(layout):
        if qualified:
            form = " ".join("NAME" if token == name else token for token in tokens)
            classes.setdefault(form, []).append(index)
    if not classes:
        raise SemanticError("the pinned declaration has no volatile member to permute")
    rotated = {}
    for form, slots in sorted(classes.items()):
        if len(slots) < 2:
            raise SemanticError(f"at least two pinned members of the form `{form}` are needed to "
                                "permute them; a lone member could not be told from its slot")
        shift = len(slots) // 2
        rotated.update({slots[(position + shift) % len(slots)]: layout[slot][1]
                        for position, slot in enumerate(slots)})
    parts = []
    for index, (tokens, name, _, _, _) in enumerate(layout):
        if index in rotated:
            tokens = [rotated[index] if token == name else token for token in tokens]
        parts.append(" ".join(tokens) + ";")
    symbol = declaration_tokens(declaration)[-2]
    text = "extern struct { " + " ".join(parts) + " } " + symbol + ";"
    new_layout, new_size = members(text)
    old = {name: offset for _, name, offset, _, _ in layout}
    mapping = {}
    for _, name, offset, _, qualified in new_layout:
        if qualified:
            if offset == old[name]:
                raise SemanticError("the perturbed layout left a pinned member in place")
            mapping[old[name]] = offset
        elif offset != old[name]:
            raise SemanticError("the perturbed layout moved an unpinned member")
    widths = {offset: width for _, _, offset, width, qualified in layout if qualified}
    if new_size != size or sorted(mapping) != sorted(mapping.values()) or \
            any(widths[old_offset] != widths[new_offset] for old_offset, new_offset in mapping.items()):
        raise SemanticError("the perturbed layout changed the object")
    return text, mapping, new_size


def replace_pinned(preprocessed, declaration, replacement):
    """the preprocessed text with the pinned declaration's one occurrence rewritten.

    The declaration's tokens must occur exactly once (the preprocessor-bypass
    rules in plausible.py keep macros, pasting and computed includes from
    changing them); otherwise the rewrite cannot be trusted.
    """
    pattern = r"\s*".join(r"\b" + re.escape(token) + r"\b" if re.match(r"\w", token)
                          else re.escape(token) for token in declaration_tokens(declaration))
    found = list(re.finditer(pattern, preprocessed))
    if len(found) != 1:
        raise SemanticError(f"the pinned declaration occurs {len(found)} times in the preprocessed "
                            "source; it must occur exactly once to be rewritten")
    start, end = found[0].span()
    return preprocessed[:start] + replacement(preprocessed[start:end]) + preprocessed[end:]


def strip_pinned_volatile(preprocessed, declaration):
    """the preprocessed text with `volatile` removed from the pinned declaration only"""
    return replace_pinned(preprocessed, declaration, lambda text: re.sub(
        r"\bvolatile\b", lambda match: " " * len(match[0]), text))


def perturb_pinned(preprocessed, declaration):
    """the preprocessed text with the pinned declaration replaced by its perturbed form"""
    return replace_pinned(preprocessed, declaration, lambda text: perturbed_declaration(declaration)[0])


SCALAR_TYPES = {"u8", "s8", "u16", "s16", "u32", "s32", "vu8", "vs8", "vu16", "vs16", "vu32",
                "vs32", "bool8", "bool16", "bool32", "int", "char", "short", "long", "unsigned",
                "signed", "float"}
QUALIFIERS = {"const", "volatile", "register", "extern", "static", "inline", "__inline__"}


def file_scope(preprocessed):
    """file-scope text: directives and linemarkers dropped, brace bodies folded to `;`"""
    text = re.sub(r"(?m)^[ \t]*#.*$", ";", preprocessed)
    while True:
        folded = re.sub(r"\{[^{}]*\}", ";", text)
        if folded == text:
            return text
        text = folded


def argument_words(declaration):
    """argument words of one parameter or return type, or None if not one word"""
    tokens = [t for t in re.findall(r"[A-Za-z_]\w*|\*|\S", declaration) if t not in QUALIFIERS]
    if "*" in tokens:
        return 1 if "(" not in tokens and "[" not in tokens else None
    names = [t for t in tokens if re.fullmatch(r"[A-Za-z_]\w*", t)]
    types = [t for t in names if t in SCALAR_TYPES]
    if not types or types.count("long") > 1 or len(names) - len(types) > 1:
        return None
    return 1


def function_signature(scope, name):
    """(returns a value, argument words or None) for a name.

    Every file-scope declaration or definition must agree.  The argument
    count is None (unknown) without a prototype, for `()` or `...`; a
    parameter or return value that is not a scalar or pointer of one word
    fails closed.
    """
    found = set()
    for match in re.finditer(r"(?:^|;)([^;]*?)\b" + re.escape(name) + r"\s*\(([^;]*?)\)\s*(?=;)", scope):
        prefix, parameters = match[1], match[2].strip()
        if "(" in parameters or ")" in parameters or "(" in prefix:
            raise SemanticError(f"the declaration of {name} is too complex to read its signature")
        returns = prefix.split() and [t for t in prefix.split() if t not in QUALIFIERS] != ["void"]
        if returns and argument_words(prefix) is None:
            raise SemanticError(f"{name} returns a value that is not one scalar or pointer word")
        if parameters == "void":
            arity = 0
        elif not parameters or "..." in parameters:
            arity = None
        else:
            words = [argument_words(parameter) for parameter in parameters.split(",")]
            if None in words:
                raise SemanticError(f"a parameter of {name} is not one scalar or pointer word")
            arity = sum(words)
        found.add((bool(returns), arity))
    if len(found) > 1:
        raise SemanticError(f"the file-scope declarations of {name} disagree")
    return found.pop() if found else (True, None)


# ---------------------------------------------------------------- expressions

def contains(expression, atom):
    """does atom occur anywhere in expression, including linear terms?"""
    if expression == atom:
        return True
    if not isinstance(expression, tuple):
        return False
    if expression[0] == "lin":
        return any(contains(term, atom) for term, _ in expression[2])
    return any(contains(part, atom) for part in expression[1:])


def carries(value, atom):
    """does value compute with atom as an address?  A load's value is the
    memory's content, not its address, so loads are not searched."""
    if value == atom:
        return True
    if not isinstance(value, tuple) or value[0] == "load":
        return False
    if value[0] == "lin":
        return any(carries(term, atom) for term, _ in value[2])
    return any(carries(part, atom) for part in value[1:])


def linear(expression):
    """(constant, {term: coefficient}) of an expression"""
    if isinstance(expression, int):
        return expression & MASK, {}
    if expression[0] == "lin":
        return expression[1], dict(expression[2])
    return 0, {expression: 1}


def make_linear(constant, terms):
    terms = {term: coefficient & MASK for term, coefficient in terms.items() if coefficient & MASK}
    constant &= MASK
    if not terms:
        return constant
    if constant == 0 and len(terms) == 1 and next(iter(terms.values())) == 1:
        return next(iter(terms))
    return ("lin", constant, tuple(sorted(terms.items(), key=repr)))


def add(a, b, sign=1):
    ca, ta = linear(a)
    cb, tb = linear(b)
    for term, coefficient in tb.items():
        ta[term] = ta.get(term, 0) + sign * coefficient
    return make_linear(ca + sign * cb, ta)


def scale(a, factor):
    constant, terms = linear(a)
    return make_linear(constant * factor, {term: c * factor for term, c in terms.items()})


def operation(name, a, b):
    if isinstance(a, int) and isinstance(b, int):
        return {"and": a & b, "orr": a | b, "eor": a ^ b, "mul": a * b}[name] & MASK
    if name == "mul":
        if isinstance(a, int) or isinstance(b, int):
            return scale(b, a) if isinstance(a, int) else scale(a, b)
    elif isinstance(b, int) or isinstance(a, int):
        constant, other = (a, b) if isinstance(a, int) else (b, a)
        if name == "and" and constant == 0:
            return 0
        if (name == "and" and constant == MASK) or (name in ("orr", "eor") and constant == 0):
            return other
        if name == "and" and is_zero_extended(other, constant):
            return other
    elif a == b:
        return 0 if name == "eor" else a
    return (name,) + tuple(sorted((a, b), key=repr))


def is_zero_extended(value, mask):
    widths = {0xFF: 8, 0xFFFF: 16}
    if mask not in widths or not isinstance(value, tuple):
        return False
    if value[0] == "load" and value[1] * 8 <= widths[mask]:
        return True
    return value[0] == "trunc" and value[1] <= widths[mask]


def shift(name, value, amount):
    if not isinstance(amount, int):
        return (name, value, amount)
    amount &= 0xFF
    if amount == 0:
        return value
    if isinstance(value, int):
        if name == "lsl":
            return (value << amount) & MASK if amount < 32 else 0
        if name == "lsr":
            return value >> amount if amount < 32 else 0
        if name == "asr":
            signed = value - (1 << 32) if value & 0x80000000 else value
            return (signed >> min(amount, 31)) & MASK
        amount %= 32
        return ((value >> amount) | (value << (32 - amount))) & MASK
    if name == "lsl":
        return scale(value, 1 << amount) if amount < 32 else 0
    return (name, value, amount)


def truncate(value, bits):
    if bits == 32:
        return value
    if isinstance(value, int):
        return value & ((1 << bits) - 1)
    if is_zero_extended(value, (1 << bits) - 1):
        return value
    if isinstance(value, tuple) and value[0] == "trunc" and value[1] >= bits:
        return ("trunc", bits, value[2])
    return ("trunc", bits, value)


def sign_extend(value, bits):
    if isinstance(value, int):
        value &= (1 << bits) - 1
        return (value - (1 << bits)) & MASK if value >> (bits - 1) else value
    return ("sext", bits, value)


def show(value):
    if isinstance(value, int):
        return hex(value)
    if value == SP:
        return "sp"
    if value[0] == "sym":
        return value[1]
    if value[0] == "lin":
        parts = [show(term) if coefficient == 1 else f"{show(term)}*{hex(coefficient)}"
                 for term, coefficient in value[2]]
        return "(" + " + ".join(parts + ([hex(value[1])] if value[1] else [])) + ")"
    return value[0] + "(" + ", ".join(show(part) if isinstance(part, (int, tuple)) else str(part)
                                      for part in value[1:]) + ")"


# ---------------------------------------------------------------- assembly

def split_operands(text):
    parts, depth, current = [], 0, ""
    for character in text:
        if character in "[{":
            depth += 1
        elif character in "]}":
            depth -= 1
        if character == "," and depth == 0:
            parts.append(current.strip())
            current = ""
        else:
            current += character
    if current.strip():
        parts.append(current.strip())
    return parts


def parse_word(text):
    text = text.strip()
    if re.fullmatch(r"-?(?:0[xX][0-9A-Fa-f]+|[0-9]+)", text):
        return int(text, 0) & MASK
    found = re.fullmatch(r"([A-Za-z_.$][\w.$]*)\s*(?:([+-])\s*(0[xX][0-9A-Fa-f]+|[0-9]+))?", text)
    if found is None:
        raise SemanticError(f"unsupported literal word `{text}`")
    if found[1].startswith(".L"):
        return ("code", found[1])
    offset = int(found[3], 0) * (-1 if found[2] == "-" else 1) if found[3] else 0
    return make_linear(offset, {("sym", found[1]): 1})


def parse_assembly(text):
    """({function name: (instructions, labels, pools)}, lines outside functions)

    instructions are (mnemonic, operands, text); labels map a code label to
    the index of the next instruction; pools map a label to the `.word`
    values from it to the next instruction or directive.
    """
    functions, outside, current, thumb_func, name = {}, [], None, False, None
    for raw in text.splitlines():
        line = raw.split("@", 1)[0].strip()
        if not line:
            continue
        if re.match(r"\.(?:code\s+32|arm)\b", line):
            raise SemanticError("ARM-mode code is not modelled")
        label = re.fullmatch(r"([A-Za-z_.$][\w.$]*):", line)
        if current is None:
            if label and thumb_func:
                if label[1] in functions:
                    raise SemanticError(f"function {label[1]} is defined twice")
                name, thumb_func, pending, owners = label[1], False, [], []
                current = functions[name] = ([], {}, {})
                continue
            if line == ".thumb_func":
                thumb_func = True
            outside.append(re.sub(r"\s+", " ", line))
            continue
        instructions, labels, pools = current
        if re.match(r"\.size\s+" + re.escape(name) + r"\s*,", line):
            current = None
            outside.append(re.sub(r"\s+", " ", line))
            continue
        if label:
            pending.append(label[1])
            labels[label[1]] = len(instructions)
            continue
        if line.startswith(".word"):
            for owner in pending:
                pools[owner] = []
            owners, pending = owners + pending, []
            if not owners:
                raise SemanticError("literal word without a label")
            word = parse_word(line[len(".word"):])
            for owner in owners:
                pools[owner].append(word)
            continue
        pending, owners = [], []
        if line.startswith("."):
            if not re.match(r"\.(?:align|pool|ltorg)\b", line):
                raise SemanticError(f"unsupported directive inside a function: `{line}`")
            continue
        mnemonic, _, operands = re.sub(r"\s+", " ", line).partition(" ")
        instructions.append((mnemonic.lower(), split_operands(operands), line))
    if current is not None:
        raise SemanticError("unterminated function in the compiler output")
    return functions, outside


# ---------------------------------------------------------------- execution

class NeedDecision(Exception):
    pass


class Record:
    """one executed instruction, for the dataflow rules"""

    def __init__(self, index, text, kind="alu", reads=(), writes=(), **fields):
        self.index, self.text, self.kind = index, text, kind
        self.reads, self.writes = set(reads), set(writes)
        self.address = self.width = self.value_register = None
        self.signed = self.forwarded = self.copy = self.constant = self.self_assignment = False
        self.immediate = False
        self.guarded, self.derived = set(), None
        self.__dict__.update(fields)


class Path:
    def __init__(self, decisions, conditions, trace, records):
        self.decisions, self.conditions = decisions, conditions
        self.trace, self.records = trace, records


def register(operand):
    operand = REGISTER_ALIASES.get(operand.lower(), operand.lower())
    if re.fullmatch(r"r(?:[0-9]|1[0-2])|sp|lr|pc", operand):
        return operand
    return None


def immediate(operand):
    found = re.fullmatch(r"#\s*(-?(?:0[xX][0-9A-Fa-f]+|[0-9]+))", operand.strip())
    return int(found[1], 0) & MASK if found else None


def register_list(operand):
    found = re.fullmatch(r"\{([^{}]*)\}", operand.strip())
    if found is None:
        raise SemanticError(f"unsupported register list `{operand}`")
    names = []
    for part in found[1].split(","):
        part = part.strip()
        bounds = re.fullmatch(r"r([0-7])\s*-\s*r([0-7])", part)
        if bounds:
            names += [f"r{n}" for n in range(int(bounds[1]), int(bounds[2]) + 1)]
        elif register(part):
            names.append(register(part))
        else:
            raise SemanticError(f"unsupported register list `{operand}`")
    order = [f"r{n}" for n in range(13)] + ["sp", "lr", "pc"]
    return sorted(set(names), key=order.index)


def is_stack(address):
    return set(linear(address)[1]) == {SP} and linear(address)[1][SP] == 1


def global_symbol(address):
    terms = linear(address)[1]
    if len(terms) == 1:
        (term, coefficient), = terms.items()
        if coefficient == 1 and isinstance(term, tuple) and term[0] == "sym":
            return term[1]
    return None


def signed32(value):
    return value - (1 << 32) if value & 0x80000000 else value


def evaluate(code, flags):
    """True/False when the flags decide the condition, else None"""
    kind, n, z, c, v = flags[0], None, None, None, None
    if kind == "cmp" and flags[1] == flags[2]:
        n, z, c, v = False, True, True, False
    elif kind in ("cmp", "cmn") and isinstance(flags[1], int) and isinstance(flags[2], int):
        a, b = flags[1], flags[2]
        if kind == "cmp":
            result = (a - b) & MASK
            c, v = a >= b, bool(((a ^ b) & (a ^ result)) >> 31)
        else:
            result = (a + b) & MASK
            c, v = a + b > MASK, bool((~(a ^ b) & (a ^ result) & MASK) >> 31)
        n, z = bool(result >> 31), result == 0
    elif kind == "nz" and isinstance(flags[1], int):
        n, z = bool(flags[1] >> 31), flags[1] == 0
    else:
        return None

    def negate(value):
        return None if value is None else not value

    def both(a, b):
        return None if a is None or b is None else a and b

    table = {"eq": z, "ne": negate(z), "mi": n, "pl": negate(n), "cs": c, "hs": c,
             "cc": negate(c), "lo": negate(c), "vs": v, "vc": negate(v),
             "hi": both(c, negate(z)), "ls": negate(both(c, negate(z))),
             "ge": None if v is None else n == v, "lt": None if v is None else n != v,
             "gt": None if v is None else both(negate(z), n == v),
             "le": None if v is None else negate(both(negate(z), n == v))}
    return table.get(code)


class Executor:
    """symbolic execution of one agbcc Thumb function along one path"""

    def __init__(self, name, function, signatures, label, layout, interfaces=None):
        self.name, self.label = name, label
        self.instructions, self.labels, self.pools = function
        self.signatures, self.interfaces = signatures, interfaces
        self.symbol, self.size, self.pinned = layout

    def check_address(self, address, width, text, multiple=False, derived=False):
        """fail closed unless an access to the object is `symbol + constant` inside it,
        the constant comes from immediates and literal words only (derived: an
        address register holds a value read back from memory), and an access
        that overlaps a pinned member is exactly that member"""
        atom = ("sym", self.symbol)
        if not contains(address, atom):
            return
        constant, terms = linear(address)
        if multiple:
            self.fail(text, f"a multi-register transfer touches {self.symbol}")
        if derived:
            # A pinned member's offset can reach a value only through memory:
            # a store through that member of another object of the type (a
            # stack copy, `__typeof__`) read back at a fixed offset.  Such an
            # offset would follow the permutation without being the member.
            self.fail(text, f"the address of this {self.symbol} access is computed from a value "
                      "read back from memory; only immediates and literal words may build an "
                      "object offset")
        if terms != {atom: 1}:
            self.fail(text, f"the address {show(address)} combines {self.symbol} with other "
                      "terms; only constant member offsets are modelled")
        offset = signed32(constant)
        if offset < 0 or offset + width > self.size:
            self.fail(text, f"the access at {self.symbol}{offset:+#x} lies outside the object")
        for start, size in sorted(self.pinned.items()):
            if start < offset + width and offset < start + size and (start, size) != (offset, width):
                self.fail(text, f"a {width}-byte access at {self.symbol}{offset:+#x} overlaps a pinned "
                          f"byte of the {size}-byte member at {self.symbol}{start:+#x}; only an access "
                          "of exactly that member, through its name, may touch it")

    def fail(self, record_text, message):
        where = f" at `{record_text}`" if record_text else ""
        raise SemanticError(f"{self.label} compile of {self.name}: {message}{where}")

    def value(self, operand, text):
        name = register(operand)
        if name == "pc":
            self.fail(text, "pc-relative arithmetic is not modelled")
        if name:
            return self.regs[name]
        constant = immediate(operand)
        if constant is None:
            self.fail(text, f"unsupported operand `{operand}`")
        return constant

    def target(self, operand, text):
        if operand not in self.labels:
            self.fail(text, f"branch to unknown label `{operand}`")
        return self.labels[operand]

    def run(self, decisions):
        self.regs = {f"r{n}": (("arg", n) if n < 4 else ("entry", f"r{n}")) for n in range(13)}
        self.regs.update(sp=SP, lr=("entry", "lr"))
        self.flags = ("entry",)
        self.memory, self.trace, self.records = [], [], []
        self.escaped, self.known, self.conditions = False, {}, []
        self.frame_base = None
        # registers and flags holding a value read back from memory: any load
        # but a literal word or a word reload of a clean word store (see
        # check_address and decide)
        self.derived, self.flags_derived = set(), False
        self.load_clean = False
        self.decisions = list(decisions)
        pc, steps = 0, 0
        while True:
            steps += 1
            if steps > MAX_STEPS:
                raise SemanticError(f"{self.label} compile of {self.name}: path exceeds {MAX_STEPS} "
                                    "instructions (loops with unknown exit conditions are not modelled)")
            if pc >= len(self.instructions):
                raise SemanticError(f"{self.label} compile of {self.name}: execution runs off the end")
            result = self.step(pc, *self.instructions[pc])
            if result == "return":
                return Path(list(decisions), self.conditions, self.trace, self.records)
            pc = pc + 1 if result is None else result

    def decide(self, code, text):
        known = evaluate(code, self.flags)
        if known is not None and not self.flags_derived:
            return known
        # Flags computed from a value read back from memory decide nothing by
        # themselves, even when the executor knows the value: the value could
        # be a store through a pinned member of another object of the type (a
        # stack copy) read back at a fixed offset, which moves with the
        # permutation.  Such a condition is a decision instead, imposed alike
        # on every compile and compared there, so no branch can follow the
        # layout.
        # A condition and its inverse are one decision, recorded under one
        # spelling: agbcc writes `bne .LCB; b .L @long jump` for a far
        # `beq .L`, so the two compiles may test the same flags either way.
        code = {"hs": "cs", "lo": "cc"}.get(code, code)
        canonical = min(code, INVERSE[code])
        flipped = canonical != code
        condition = (canonical, self.flags)
        if condition in self.known:
            return self.known[condition] != flipped
        if len(self.conditions) >= len(self.decisions):
            if len(self.decisions) >= MAX_DECISIONS:
                raise SemanticError(f"{self.label} compile of {self.name}: more than {MAX_DECISIONS} "
                                    "unknown branch conditions on one path (loops with unknown exit "
                                    "conditions are not modelled)")
            raise NeedDecision()
        taken = self.decisions[len(self.conditions)]
        self.conditions.append(condition)
        self.known[condition] = taken
        return taken != flipped

    # memory ---------------------------------------------------------------

    def relation(self, a, width_a, b, width_b, private=False):
        ca, ta = linear(a)
        cb, tb = linear(b)
        if ta == tb:
            distance = signed32((ca - cb) & MASK)
            if distance == 0 and width_a == width_b:
                return "same"
            if distance >= width_b or -distance >= width_a:
                return "disjoint"
            return "overlap"
        if is_stack(a) != is_stack(b) and (not self.escaped or private):
            return "disjoint"
        ga, gb = global_symbol(a), global_symbol(b)
        if ga and gb and ga != gb:
            return "disjoint"
        return "overlap"

    def load(self, width, signed, address, text):
        # Saved-register slots stay private even after the frame escapes:
        # the escaping pointer addresses locals, not the push area.
        saved = is_stack(address) and any(entry[0] == "store" and entry[5] and entry[2] == address
                                          for entry in self.memory)
        stack = is_stack(address) and (not self.escaped or saved)
        version, forwarded = "entry", None
        self.load_clean = False
        for entry in reversed(self.memory):
            if entry[0] == "call":
                if not stack:
                    version = ("call", entry[1])
                    break
                continue
            _, stored_width, stored_address, stored, event, _, derived = entry
            relation = self.relation(address, width, stored_address, stored_width, saved)
            if relation == "same":
                forwarded = stored
                # Only a store wider than every pinned member can be reloaded
                # clean: a store through a pinned member is never that wide.
                # Derived from PINNED_WIDTHS, so admitting word members makes
                # no reload clean (fails closed) rather than breaking this.
                self.load_clean = width == 4 and width > max(PINNED_WIDTHS) and not derived
                break
            if relation == "overlap":
                if event is None:
                    self.fail(text, "partially overlapping stack access")
                version = ("store", event)
                break
        if forwarded is not None:
            value = forwarded
        else:
            value = ("load", width, self.observed(address), version)
        if signed:
            value = sign_extend(value, width * 8)
        return value, forwarded is not None

    def current(self, width, address):
        return self.load(width, False, address, "")[0]

    def observed(self, address):
        """an address as the trace records it: escaped stack slots relative to the escape"""
        if is_stack(address) and self.frame_base is not None:
            return ("frame", signed32(linear(address)[0]) - self.frame_base)
        return address

    def escape(self, values, text):
        """the frame becomes visible to other code through a pointer in values.

        The contents of every local (non-saved) frame byte at that moment
        join the trace, relative to the first escaping pointer, with the
        stores applied byte by byte in program order; each escape takes a
        new snapshot.  So two compiles cannot hand over different stack data,
        on either side of the pointer.  From then on stack stores are
        observable and calls may change the frame.
        """
        pointers = [value for value in values if carries(value, SP)]
        if not pointers:
            return
        for pointer in pointers:
            if not is_stack(pointer):
                self.fail(text, f"a stack address escapes as {show(pointer)}")
        if self.frame_base is None:
            self.frame_base = min(signed32(linear(pointer)[0]) for pointer in pointers)
        self.escaped = True
        frame = {}
        for entry in self.memory:
            if entry[0] != "store" or not is_stack(entry[2]) or entry[5]:
                continue
            offset, width, value = signed32(linear(entry[2])[0]), entry[1], entry[3]
            for byte in range(width):
                if width == 1:
                    part = value
                elif isinstance(value, int):
                    part = (value >> (8 * byte)) & 0xFF
                else:
                    part = ("byte", byte, value)
                frame[offset + byte - self.frame_base] = part
        self.trace.append(("escape", tuple(sorted(frame.items()))))

    def store(self, width, address, value, saved=False, text="", derived=False):
        value = truncate(value, width * 8)
        if carries(value, ("sym", self.symbol)):
            self.fail(text, f"the address of {self.symbol} is stored to memory")
        event = None
        if not is_stack(address):
            self.escape([value], text)
        if not is_stack(address) or self.escaped:
            event = len(self.trace)
            self.trace.append(("store", width, self.observed(address), value))
        self.memory.append(("store", width, address, value, event, saved, derived))
        return value

    def call(self, target, text, record):
        if isinstance(target, str) and target in RUNTIME_ARITY:
            count, trusted = RUNTIME_ARITY[target], True
        elif isinstance(target, tuple) and target[0] == "swi":
            count, trusted = 4, False        # BIOS calls take r0-r3 only
        elif isinstance(target, str) and self.signatures.get(target, (None, None))[1] is not None:
            count, trusted = self.signatures[target][1], False
        else:
            self.fail(text, "the callee has no prototype with a fixed argument list, so its "
                      "arguments cannot be compared")
        arguments = [self.regs[f"r{n}"] for n in range(min(count, 4))]
        for n in range(4, count):
            arguments.append(self.load(4, False, add(self.regs["sp"], 4 * (n - 4)), text)[0])
        # No prototype is trusted to name every register the callee reads:
        # a dead load into an unnamed argument register could be a hidden
        # argument, so r0-r3 all count as read (only runtime helpers with a
        # known interface are exact) unless the callee's own ROM code shows
        # which of them it reads (RomInterfaces).  Then exactly those count
        # as read, and only the registers it overwrites on every path count
        # as written; a register it leaves alone stays live past the call.
        named = {f"r{n}" for n in range(min(count, 4))}
        interface = None
        if not trusted and isinstance(target, str) and self.interfaces is not None:
            interface = self.interfaces(target)
        if interface is None:
            record.guarded = set() if trusted else set(ARGUMENT_REGISTERS) - named
        else:
            reads, writes = interface
            record.guarded, record.derived = set(reads) - named, target
            record.interface = (reads, writes)
            record.writes = set(writes) | {"lr"}
        record.reads = named | record.guarded | (record.reads - set(ARGUMENT_REGISTERS))
        if any(carries(argument, ("sym", self.symbol)) for argument in arguments):
            self.fail(text, f"the address of {self.symbol} is passed to a call")
        self.escape(arguments, text)
        event = len(self.trace)
        self.trace.append(("call", target, tuple(arguments)))
        self.memory.append(("call", event))
        self.regs["r0"] = ("ret", event)
        for name in ("r1", "r2", "r3", "r12", "lr"):
            self.regs[name] = ("clobber", event, name)
        self.derived -= {"r0", "r1", "r2", "r3", "r12", "lr"}
        self.flags, self.flags_derived = ("clobber", event), False
        self.records.append(record)

    def finish(self, text, record):
        returns = self.signatures.get(self.name, (True,))[0]
        if self.regs["sp"] != SP:
            self.fail(text, "the stack is not balanced at return")
        self.trace.append(("return",) + ((self.regs["r0"],) if returns else ()))
        if returns:
            record.reads.add("r0")
        self.records.append(record)
        return "return"

    # instructions ---------------------------------------------------------

    def memory_operand(self, operand, text):
        found = re.fullmatch(r"\[\s*([^,\]]+?)\s*(?:,\s*([^\]]+?)\s*)?\]", operand)
        if found is None:
            self.fail(text, f"unsupported memory operand `{operand}`")
        base = register(found[1])
        if base is None or base == "pc":
            self.fail(text, f"unsupported base register `{found[1]}`")
        reads = {base}
        offset = 0
        if found[2]:
            index = register(found[2])
            if index:
                reads.add(index)
            offset = self.value(found[2], text)
        return add(self.regs[base], offset), reads

    def step(self, pc, mnemonic, operands, text):
        record = Record(pc, text)
        flags = self.flags
        alu = ("mov", "add", "sub", "neg", "mvn", "and", "orr", "eor", "bic", "mul",
               "lsl", "lsr", "asr", "ror")
        if mnemonic.endswith("s") and mnemonic[:-1] in alu:
            mnemonic = mnemonic[:-1]      # unified syntax spells the flag-setting forms `adds`
        regs = self.regs
        if mnemonic in alu:
            destination = register(operands[0]) if operands else None
            if destination is None or destination == "pc" or len(operands) not in (2, 3):
                if mnemonic == "mov" and destination == "pc" and len(operands) == 2:
                    return self.jump_register(operands[1], text, record)
                self.fail(text, "unsupported instruction form")
            # two-operand forms read their destination: `orr rd, rm` is rd = rd | rm
            sources = operands[1:] if len(operands) == 3 or mnemonic in ("mov", "neg", "mvn") else operands
            record.reads = {register(o) for o in sources if register(o)}
            record.writes = {destination}
            values = [self.value(o, text) for o in sources]
            sets_flags = destination not in ("sp",) and not any(register(o) in ("sp",) for o in sources)
            if mnemonic == "mov":
                result = values[0]
                record.copy = register(sources[0]) is not None
                low = [f"r{n}" for n in range(8)]
                if immediate(sources[0]) is not None:
                    self.flags = ("nz", result)
                    record.constant = record.immediate = True
                elif destination in low and register(sources[0]) in low:
                    # a low-register `mov` assembles as `adds rd, rm, #0`
                    self.flags = ("cmn", result, 0)
            elif mnemonic in ("add", "sub"):
                sign = 1 if mnemonic == "add" else -1
                result = add(values[0], values[1], sign)
                record.copy = mnemonic == "add" and values[1] == 0 and register(sources[0]) is not None \
                    and immediate(sources[1]) is not None
                high = len(operands) == 2 and register(operands[1]) and \
                    (destination not in [f"r{n}" for n in range(8)] or
                     register(operands[1]) not in [f"r{n}" for n in range(8)])
                if sets_flags and not high:
                    self.flags = ("cmp", values[0], values[1]) if sign < 0 else ("cmn", values[0], values[1])
            elif mnemonic == "neg":
                result = scale(values[0], -1)
                self.flags = ("cmp", 0, values[0])
            elif mnemonic == "mvn":
                result = add(scale(values[0], -1), 1, -1)
                self.flags = ("nz", result)
            elif mnemonic in ("lsl", "lsr", "asr", "ror"):
                amount = values[1]
                if not isinstance(amount, int):
                    amount = operation("and", amount, 0xFF)
                result = shift(mnemonic, values[0], amount)
                self.flags = ("shift", mnemonic, values[0], amount)
            else:
                b = values[1]
                if mnemonic == "bic":
                    b = add(scale(b, -1), 1, -1)
                result = operation({"bic": "and"}.get(mnemonic, mnemonic), values[0], b)
                self.flags = ("nz", result)
            # arithmetic on known constants only (`mov r0, #128; lsl r0, r0, #1`
            # builds 0x100) is constant materialisation, like an immediate mov
            record.constant = record.constant or (
                isinstance(result, int) and all(isinstance(value, int) for value in values))
            regs[destination] = result
            derived = bool(record.reads & self.derived)
            self.derived = (self.derived | {destination}) if derived else (self.derived - {destination})
            if self.flags is not flags:
                self.flags_derived = derived
            self.records.append(record)
            return None
        if mnemonic in ("cmp", "cmn", "tst"):
            if len(operands) != 2:
                self.fail(text, "unsupported instruction form")
            record.reads = {register(o) for o in operands if register(o)}
            a, b = self.value(operands[0], text), self.value(operands[1], text)
            self.flags = ("nz", operation("and", a, b)) if mnemonic == "tst" else (mnemonic, a, b)
            self.flags_derived = bool(record.reads & self.derived)
            self.records.append(record)
            return None
        if mnemonic in ("ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "str", "strb", "strh"):
            if len(operands) != 2 or register(operands[0]) in (None, "pc"):
                self.fail(text, "unsupported instruction form")
            subject = register(operands[0])
            width = 1 if mnemonic.endswith("b") else 2 if mnemonic.endswith("h") else 4
            pool = re.fullmatch(r"(\.L\w+)(?:\s*\+\s*([0-9]+))?", operands[1])
            if pool and mnemonic == "ldr":
                words = self.pools.get(pool[1])
                offset = int(pool[2] or 0)
                if words is None or offset % 4 or offset // 4 >= len(words):
                    self.fail(text, "literal load outside a pool")
                record.kind, record.writes = "literal", {subject}
                regs[subject] = words[offset // 4]
                self.derived.discard(subject)
                self.records.append(record)
                return None
            address, reads = self.memory_operand(operands[1], text)
            derived = bool(reads & self.derived)
            self.check_address(address, width, text, derived=derived)
            record.address, record.width = address, width
            if mnemonic.startswith("ldr"):
                record.kind, record.reads, record.writes = "load", reads, {subject}
                record.signed = mnemonic in ("ldrsb", "ldrsh")
                regs[subject], record.forwarded = self.load(width, record.signed, address, text)
                record.value = regs[subject]
                if derived or not self.load_clean or record.signed:
                    self.derived.add(subject)
                else:
                    self.derived.discard(subject)
            else:
                record.kind, record.reads, record.value_register = "store", reads | {subject}, subject
                value = truncate(regs[subject], width * 8)
                record.self_assignment = isinstance(value, tuple) and value[0] == "load" and \
                    value == self.current(width, address)
                record.value = self.store(width, address, regs[subject], text=text,
                                          derived=derived or subject in self.derived)
            self.records.append(record)
            return None
        if mnemonic in ("push", "stmia", "stm", "pop", "ldmia", "ldm"):
            if mnemonic in ("push", "pop"):
                if len(operands) != 1:
                    self.fail(text, "unsupported instruction form")
                base, names, writeback = "sp", register_list(operands[0]), True
            else:
                if len(operands) != 2 or not operands[0].endswith("!"):
                    self.fail(text, "unsupported instruction form")
                base, names, writeback = register(operands[0][:-1]), register_list(operands[1]), True
                if base is None or base in ("sp", "pc"):
                    self.fail(text, "unsupported base register")
            storing = mnemonic in ("push", "stmia", "stm")
            start = add(regs[base], -4 * len(names)) if mnemonic == "push" else regs[base]
            record.kind = "push" if storing else "pop"
            record.reads = {base} | (set(names) if storing else set())
            record.writes = {base} | (set() if storing else set(names) - {"pc"})
            loaded, clean = {}, {}
            derived = base in self.derived
            for n, name in enumerate(names):
                address = add(start, 4 * n)
                self.check_address(address, 4, text, multiple=True)
                if storing:
                    self.store(4, address, regs[name], saved=mnemonic == "push", text=text,
                               derived=derived or name in self.derived)
                else:
                    loaded[name] = self.load(4, False, address, text)[0]
                    clean[name] = self.load_clean and not derived
            if writeback:
                regs[base] = start if mnemonic == "push" else add(regs[base], 4 * len(names))
            for name, value in loaded.items():
                if name != "pc":
                    regs[name] = value
                    self.derived = (self.derived - {name}) if clean[name] else (self.derived | {name})
            if "pc" in loaded:
                if loaded["pc"] != ("entry", "lr"):
                    self.fail(text, "pop into pc of something other than the return address")
                return self.finish(text, record)
            self.records.append(record)
            return None
        if mnemonic == "b" or (mnemonic[:1] == "b" and mnemonic[1:] in INVERSE):
            if len(operands) != 1:
                self.fail(text, "unsupported branch form")
            record.kind = "branch"
            self.records.append(record)
            if mnemonic == "b" or self.decide(mnemonic[1:], text):
                return self.target(operands[0], text)
            return None
        if mnemonic == "bl":
            if len(operands) != 1:
                self.fail(text, "unsupported call form")
            record.kind = "call"
            record.reads, record.writes = {"r0", "r1", "r2", "r3"}, {"r0", "r1", "r2", "r3", "r12", "lr"}
            via = re.fullmatch(r"_call_via_(r[0-9]|r1[0-2]|ip|fp|sl|sb|lr)", operands[0])
            target = operands[0]
            if via:
                name = register(via[1])
                record.reads.add(name)
                target = ("via", regs[name])
            self.call(target, text, record)
            return None
        if mnemonic == "bx":
            if len(operands) != 1:
                self.fail(text, "unsupported instruction form")
            return self.jump_register(operands[0], text, record)
        if mnemonic in ("swi", "svc"):
            record.kind = "call"
            record.reads, record.writes = {"r0", "r1", "r2", "r3"}, {"r0", "r1", "r2", "r3", "r12", "lr"}
            self.call(("swi", operands[0] if operands else ""), text, record)
            return None
        if mnemonic == "nop":
            self.records.append(record)
            return None
        self.fail(text, f"unsupported instruction `{mnemonic}`")

    def jump_register(self, operand, text, record):
        name = register(operand)
        if name is None:
            self.fail(text, "unsupported jump operand")
        record.kind, record.reads = "return", {name}
        if self.regs[name] == ("entry", "lr"):
            return self.finish(text, record)
        self.fail(text, "computed jumps are not modelled")


# ---------------------------------------------------------------- callee interfaces

ROM_BASE = 0x08000000
MAX_CALLEE_BYTES = 0x4000
MAX_CALLEE_DEPTH = 8
MAX_CALLEES = 64
UNKNOWN_INTERFACE = (frozenset(ARGUMENT_REGISTERS), frozenset())


class RomInterfaces:
    """which of r0-r3 an indexed Thumb callee reads, derived from its ROM bytes.

    For `bl func_XXXXXXXX` the callee is the indexed Thumb function at that
    address (the name is what the byte match links it to).  Its CFG comes
    from analyze.refine_function over the indexed span, and a dataflow pass
    over that CFG finds
    * reads: the argument registers some path reads before writing them, and
    * writes: the argument registers every path overwrites before returning.
    Register effects are capstone's (pushes and stores count as reads).  A
    call inside the callee reads what its own callee reads, transitively, and
    writes what that callee writes on every path; recursion, more than
    MAX_CALLEE_DEPTH levels or MAX_CALLEES callees, a CFG that does not close,
    a word switch, an unindexed or non-Thumb target, and anything else this
    does not model give UNKNOWN_INTERFACE (reads r0-r3, writes none), so the
    analysis fails closed.  A register the callee never reads cannot carry
    information into it, and one it overwrites on every path carries none
    out, so a dead load in such a register is dead across the call.
    Only ROM bytes and the function index are used, never source.
    """

    def __init__(self, rom, functions):
        self.rom, self.functions = rom, functions
        self.cache, self.budget, self.names, self.inexact = {}, MAX_CALLEES, {}, {}

    def __call__(self, name):
        """(reads, writes) for a callee name, or None when nothing could be derived.

        None keeps the strict rule (the call reads r0-r3).  The answer is
        fixed per name on first use, so every compile of the function sees
        the same interface whatever the budget does later.
        """
        found = re.fullmatch(r"func_([0-9A-F]{8})", name)
        if found is None:
            return None
        if name not in self.names:
            self.inexact = {}
            summary = self.summary(int(found[1], 16), ())[:2]
            self.names[name] = None if summary == UNKNOWN_INTERFACE else summary
        return self.names[name]

    def summary(self, address, active):
        """(reads, writes, exact); exact is False when a bound, not the code, decided"""
        if address in self.cache:
            return self.cache[address] + (True,)
        if address in self.inexact:
            # an over-approximation, so reusing it within one top-level
            # call is sound and keeps revisits from spending the budget
            return self.inexact[address] + (False,)
        if address in active or len(active) >= MAX_CALLEE_DEPTH or self.budget <= 0:
            return UNKNOWN_INTERFACE + (False,)
        self.budget -= 1
        try:
            instructions, entry, returns = self.control_flow(address)
        except Exception:       # anything unmodelled fails closed
            self.cache[address] = UNKNOWN_INTERFACE
            return UNKNOWN_INTERFACE + (True,)
        arguments = frozenset(ARGUMENT_REGISTERS)
        written_at, pending, reads, ends, exact = {entry: frozenset()}, [entry], set(), None, True
        while pending:
            position = pending.pop()
            read, write, successors, target = instructions[position]
            if target is not None:
                read, write, inner = self.summary(target, active + (address,))
                exact = exact and inner
            # the must-written sets only shrink, so each revisit can only add reads
            written = written_at[position]
            reads |= (read & arguments) - written
            written = written | (write & arguments)
            if position in returns:
                ends = written if ends is None else ends & written
            for successor in successors:
                merged = written_at[successor] & written if successor in written_at else written
                if written_at.get(successor) != merged:
                    written_at[successor] = merged
                    pending.append(successor)
        result = (frozenset(reads), ends or frozenset())
        (self.cache if exact else self.inexact)[address] = result
        return result + (exact,)

    def control_flow(self, address):
        """({position: (reads, writes, successors, call target)}, entry, return sites)"""
        from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs     # before analyze, which exits without it
        from capstone.arm_const import ARM_OP_IMM
        import analyze
        offset = address - ROM_BASE
        if address % 2 or not 0 <= offset < len(self.rom):
            raise SemanticError("callee outside the ROM")
        data = bytes(self.rom[offset:offset + MAX_CALLEE_BYTES])
        refined = analyze.refine_function(data, address, self.functions, max_bytes=len(data),
                                          max_instructions=len(data) // 2,
                                          rom_end=ROM_BASE + len(self.rom))
        if not refined["cfg_closed"] or refined["mode"] != "thumb" or refined["word_switches"]:
            raise SemanticError("callee CFG does not close")
        calls = {int(call["site"], 16): int(call["target"], 16) for call in refined["calls"]}
        returns = {int(site, 16) for site in refined["returns"]}
        engine = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
        engine.detail = True
        instructions = {}
        for start, stop in refined["code_ranges"]:
            start, stop = int(start, 16), int(stop, 16)
            position = start
            while position < stop:
                instruction = next(engine.disasm(data[position - address:stop - address], position,
                                                 count=1), None)
                if instruction is None:
                    raise SemanticError("undecodable callee instruction")
                size, mnemonic = instruction.size, instruction.mnemonic
                read, write = (frozenset(instruction.reg_name(r) for r in registers)
                               for registers in instruction.regs_access())
                following = [position + size]
                if position in returns:
                    following = []
                elif mnemonic == "bl":
                    if position not in calls:
                        raise SemanticError("callee BL is not an indexed call")
                elif mnemonic == "b" or (mnemonic[:1] == "b" and mnemonic[1:] in INVERSE):
                    operands = instruction.operands
                    if len(operands) != 1 or operands[0].type != ARM_OP_IMM:
                        raise SemanticError("unmodelled callee branch")
                    following = [operands[0].imm] + (following if mnemonic != "b" else [])
                elif "pc" in write:
                    raise SemanticError("unmodelled callee transfer")
                instructions[position] = (read, write, following, calls.get(position))
                position += size
            if position != stop:
                raise SemanticError("callee code range ends inside an instruction")
        if len(instructions) != refined["instrs"] or set(calls) - set(instructions) or \
                returns - set(instructions) or address not in instructions or \
                any(successor not in instructions
                    for _, _, successors, _ in instructions.values() for successor in successors):
            raise SemanticError("callee CFG and decoding disagree")
        return instructions, address, returns


# ---------------------------------------------------------------- comparison

def explore(name, function, signatures, label, layout, interfaces=None):
    paths, pending = [], [[]]
    while pending:
        decisions = pending.pop()
        try:
            path = Executor(name, function, signatures, label, layout, interfaces).run(decisions)
        except NeedDecision:
            pending += [decisions + [False], decisions + [True]]
            continue
        paths.append(path)
        if len(paths) > MAX_PATHS:
            raise SemanticError(f"{name} has more than {MAX_PATHS} paths; the semantic check is bounded")
    return paths


def replay(name, function, signatures, label, decisions, layout, interfaces=None):
    try:
        return Executor(name, function, signatures, label, layout, interfaces).run(decisions)
    except NeedDecision:
        raise SemanticError(f"{name}: the stripped compile branches where the real one does not")


def describe(record):
    return f"`{record.text}` (instruction {record.index + 1})"


def object_offset(address, symbol, size):
    constant, terms = linear(address)
    if terms == {("sym", symbol): 1}:
        offset = signed32(constant)
        return offset if -4 < offset < size else None
    return None


def dead(records, position, destination, relied=None):
    """True if overwritten before any use, False if used, or the call record
    whose source-supplied prototype leaves the register's use unknown.

    relied, if given, collects the calls crossed only because their ROM
    interface shows the callee does not read the register."""
    for record in records[position + 1:]:
        if destination in record.guarded:
            return record
        if destination in record.reads:
            return False
        if relied is not None and record.derived and destination in ARGUMENT_REGISTERS:
            relied.add(record)
        if destination in record.writes:
            return True
    return True


def read_modify_write_store(records, position, address, width):
    """the position of the store this dead load belongs to, or None.

    agbcc computes a volatile bit-field store's value before the
    read-modify-write load; the only instructions it leaves between that
    load and the `strb`/`strh` are immediate `mov`s and arithmetic on known
    constants (its own value - `mov #128; lsl #1` for a halfword 0x100 - or
    a later store's hoisted constant in 08050D50) and register copies or
    literal loads (08122C6C copies the address).  Apart from an immediate
    `mov`, a copy or literal load must write a register whose value reaches
    the store's operands (its value or address register) through copies,
    and constant arithmetic must reach the store's value register.
    Anything else in between - arithmetic on unknown values, another memory
    access, a call or a branch - means the load was not emitted by the
    store.  The store must have the load's width and address.
    """
    between = []
    for later in range(position + 1, len(records)):
        record = records[later]
        if record.kind == "store":
            if record.width != width or record.address != address:
                return None
            def feeding(registers):
                """the steps whose result reaches registers through copies"""
                live, found = set(registers), set()
                for step in reversed(between):
                    if step.writes & live:
                        found.add(step.index)
                        live -= step.writes
                        if step.copy:
                            live |= step.reads
                return found
            operands, value = feeding(record.reads), feeding({record.value_register})
            for step in between:
                if step.immediate:
                    continue
                if step.constant and not step.copy and step.kind != "literal":
                    if step.index not in value:      # constant arithmetic builds the stored value
                        return None
                elif step.index not in operands:
                    return None
            return later
        if not (record.kind == "literal" or record.copy or record.constant):
            return None
        between.append(record)
    return None


def chained_reread(records, position, pinned_width):
    """is this load the re-read of `a = (b = v)` with volatile `b`?

    The forwarding store of the load's width to the same member must be the
    immediately preceding memory access, with only register arithmetic in
    between, and the value must reach (through register copies) the next
    store, which is a store to a pinned member of that member's width;
    apart from that store's own read-modify-write load no memory access,
    call or branch may intervene, and the value is used nowhere else.
    pinned_width maps an address to its pinned member's width, or None.
    """
    load = records[position]
    earlier = position - 1
    while earlier >= 0 and records[earlier].kind in ("alu", "literal"):
        earlier -= 1
    if earlier < 0 or records[earlier].kind != "store" or records[earlier].width != load.width or \
            records[earlier].address != load.address:
        return False
    tracked, store, loads = set(load.writes), None, []
    for record in records[position + 1:]:
        if store is None:
            if record.kind == "store":
                if record.width != pinned_width(record.address) or \
                        record.value_register not in tracked or \
                        (record.reads - {record.value_register}) & tracked or \
                        any(address != record.address for address in loads) or len(loads) > 1:
                    return False
                store = record
                continue
            if record.kind == "load" and not record.reads & tracked:
                loads.append(record.address)
            elif record.kind not in ("alu", "literal"):
                return False
            elif record.reads & tracked and not (record.copy and record.reads <= tracked):
                return False
            elif record.copy and record.reads & tracked:
                tracked |= record.writes
                continue
        elif record.reads & tracked:
            return False
        tracked -= record.writes
        if not tracked:
            break
    return store is not None


def compare_function(name, real_function, stripped_function, signatures, symbol, size, pinned,
                     interfaces=None, unloaded_all_ones=False):
    def pinned_width(address):
        """the width of the pinned member that starts at address, or None"""
        return pinned.get(object_offset(address, symbol, size))

    def where(address):
        offset = object_offset(address, symbol, size)
        return f"{symbol}+{offset:#x}" if offset is not None else show(address)

    paths = explore(name, real_function, signatures, "real", (symbol, size, pinned), interfaces)
    read_modify_write, chained, unloaded, relied = set(), set(), set(), set()
    for number, path in enumerate(paths, 1):
        records = path.records
        # 4. a store must not write back the value it read from the same byte
        for record in records:
            if record.kind == "store" and pinned_width(record.address) and record.self_assignment:
                raise SemanticError(f"{name}: {describe(record)} writes back the value it read "
                                    f"from {where(record.address)} (a load/store self-assignment)")
        # 2. classify every load of the object in the real compile
        counterparts, explained_stores = [], set()
        for position, record in enumerate(records):
            if record.kind != "load" or object_offset(record.address, symbol, size) is None:
                continue
            destination = next(iter(record.writes))
            if record.width == pinned_width(record.address) and not record.signed:
                crossed = set()
                verdict = dead(records, position, destination, crossed)
                if verdict is True:
                    relied.update(call.derived + " reads {" + ", ".join(sorted(call.interface[0])) +
                                  "} writes {" + ", ".join(sorted(call.interface[1])) + "}"
                                  for call in crossed)
                if isinstance(verdict, Record) and verdict.derived:
                    raise SemanticError(
                        f"{name}: {describe(record)} loads {where(record.address)} into "
                        f"{destination}, which {verdict.derived} reads before writing it (from its "
                        "ROM code) although its prototype does not name it; the load must be "
                        "overwritten before the call")
                if isinstance(verdict, Record):
                    raise SemanticError(
                        f"{name}: {describe(record)} loads {where(record.address)} into "
                        f"{destination}, which {describe(verdict)} might take as an argument its "
                        "prototype does not name; no prototype is trusted to list every argument, "
                        "so the load must be overwritten before the call")
                if verdict:
                    store = read_modify_write_store(records, position, record.address, record.width)
                    if store is None:
                        raise SemanticError(
                            f"{name}: {describe(record)} is a dead load of {where(record.address)} "
                            "that is not directly followed by a store to the same member (only "
                            "constants and the store's own operand copies may sit between "
                            "them); only the read-modify-write load of a member store is the "
                            "qualifier's documented effect")
                    explained_stores.add(store)
                    read_modify_write.add(record.index)
                    continue
                if record.forwarded and chained_reread(records, position, pinned_width):
                    chained.add(record.index)
                    continue
            counterparts.append((record.width, record.signed, where(record.address), record))
        # 3. every store to a pinned member carries its read-modify-write load
        for position, record in enumerate(records):
            if record.kind != "store":
                continue
            offset = object_offset(record.address, symbol, size)
            if offset is None or not any(start < offset + record.width and offset < start + width
                                         for start, width in pinned.items()):
                continue
            if record.width == pinned.get(offset) and position not in explained_stores and \
                    unloaded_all_ones and record.value == (1 << 8 * record.width) - 1:
                # agbcc's combine folds `(ior (mem/v x) all-ones)` to the
                # constant and so drops this store's own load; only the
                # member's all-ones value can lose it.  The permuted compile
                # (perturbation_check, which unloaded_all_ones requires) has
                # already shown that this store follows its member's name.
                unloaded.add(record.index)
                continue
            if record.width != pinned.get(offset) or position not in explained_stores:
                raise SemanticError(f"{name}: {describe(record)} stores to {where(record.address)} "
                                    "without the read-modify-write load of a volatile member store")
        # 1. the stripped compile behaves the same on this path
        other = replay(name, stripped_function, signatures, "stripped", path.decisions, (symbol, size, pinned),
                       interfaces)
        if other.conditions != path.conditions:
            raise SemanticError(f"{name}: the real and stripped compiles branch on different "
                                f"conditions (path {number})")
        if other.trace != path.trace:
            for index, (mine, theirs) in enumerate(zip(path.trace + [None] * len(other.trace),
                                                       other.trace + [None] * len(path.trace))):
                if mine != theirs:
                    break
            raise SemanticError(f"{name}: the real and stripped compiles differ in observable "
                                f"behaviour (path {number}, event {index + 1}: real "
                                f"{show_event(mine)}, stripped {show_event(theirs)})")
        theirs = [(r.width, r.signed, where(r.address)) for r in other.records
                  if r.kind == "load" and object_offset(r.address, symbol, size) is not None]
        mine = [entry[:3] for entry in counterparts]
        if mine != theirs:
            index = next((i for i, (a, b) in enumerate(zip(mine, theirs)) if a != b), min(len(mine), len(theirs)))
            if index < len(mine):
                raise SemanticError(f"{name}: {describe(counterparts[index][3])} loads "
                                    f"{counterparts[index][2]}, which the stripped compile does not "
                                    "load there; the qualifier added a read")
            raise SemanticError(f"{name}: the stripped compile loads {theirs[index][2]} where the real "
                                "one does not")
    return len(paths), sorted(read_modify_write), sorted(chained), sorted(unloaded), sorted(relied)


def show_event(event):
    if event is None:
        return "nothing"
    if event[0] == "store":
        return f"store{event[1] * 8} {show(event[2])} <- {show(event[3])}"
    if event[0] == "call":
        target = event[1] if isinstance(event[1], str) else show(event[1][1]) if event[1][0] == "via" \
            else str(event[1])
        return f"call {target}({', '.join(show(a) for a in event[2])})"
    if event[0] == "escape":
        return "frame escape {" + ", ".join(f"{offset:+#x}: {show(value)}" for offset, value in event[1]) + "}"
    return "return" + (f" {show(event[1])}" if len(event) > 1 else "")


def normalised(lines):
    names = {}
    return [re.sub(r"\.L\d+\b", lambda m: names.setdefault(m[0], f".L#{len(names)}"), line)
            for line in lines]


def remap(expression, atom, mapping):
    """expression with every `symbol + pinned offset` replaced by its moved offset.

    Trace events are walked structurally, so containers reach here as well as
    values: a zero-argument call's argument tuple and an escape with no
    local frame bytes are both `()`.  An empty tuple holds no address and is
    its own image; the caller compares it exactly, element for element.
    """
    if not isinstance(expression, tuple) or not expression:
        return expression
    if expression[0] == "lin":
        constant, terms = linear(expression)
        if terms == {atom: 1} and signed32(constant) in mapping:
            return make_linear(mapping[signed32(constant)], terms)
        return make_linear(constant, {remap(term, atom, mapping): c for term, c in terms.items()})
    if expression == atom and 0 in mapping:
        return make_linear(mapping[0], {atom: 1})
    return tuple(remap(part, atom, mapping) if isinstance(part, tuple) else part for part in expression)


def object_accesses(records, atom):
    return [(record.kind, record.width, record.address) for record in records
            if record.address is not None and contains(record.address, atom)]


def perturbation_check(name, real_function, perturbed_function, signatures, symbol, size, pinned,
                       mapping, interfaces=None):
    """the layout-perturbed compile must follow every pinned access, and only those.

    On every path, the real compile's trace, branch conditions and object
    accesses, with each pinned offset X mapped to its permuted offset P(X),
    must equal the perturbed compile's.  The permutation keeps every other
    offset, the size and the alignment, so an access computed from anything
    but a pinned member's name has the same address in both compiles; as
    P(X) != X for every pinned X, it cannot follow the move.  Accesses that
    overlap a pinned member without being exactly it are refused by the
    executor in both compiles, so remapping an access's start is enough.
    """
    atom = ("sym", symbol)
    paths = explore(name, real_function, signatures, "real", (symbol, size, pinned), interfaces)
    for number, path in enumerate(paths, 1):
        other = replay(name, perturbed_function, signatures, "layout-perturbed", path.decisions,
                       (symbol, size, pinned), interfaces)
        mine = [(kind, width, remap(address, atom, mapping))
                for kind, width, address in object_accesses(path.records, atom)]
        theirs = object_accesses(other.records, atom)
        if mine != theirs:
            index = next((i for i, (a, b) in enumerate(zip(mine, theirs)) if a != b),
                         min(len(mine), len(theirs)))
            real_access = object_accesses(path.records, atom)[index] if index < len(mine) else None
            raise SemanticError(
                f"{name}: an access to {symbol} does not follow its member when the pinned members "
                f"move (path {number}, access {index + 1}: real "
                f"{show(real_access[2]) if real_access else 'none'}, perturbed "
                f"{show(theirs[index][2]) if index < len(theirs) else 'none'}); a pinned member may "
                "only be reached through its own name")
        if [remap(c, atom, mapping) for c in path.conditions] != other.conditions or \
                [remap(e, atom, mapping) for e in path.trace] != other.trace:
            raise SemanticError(f"{name}: the layout-perturbed compile behaves differently (path "
                                f"{number}); the source depends on where the pinned members are")
    return len(paths)


def compare(real_assembly, stripped_assembly, preprocessed, symbol, declaration, perturbed_assembly,
            interfaces=None):
    """[(function, paths, read-modify-write instructions, chained re-reads)].

    The three compiles are the source as written, with `volatile` stripped
    from the pinned declaration (strip_pinned_volatile) and with its pinned
    members permuted (perturb_pinned).  Raises SemanticError with the reason
    when the real compile differs from the stripped one by anything but the
    qualifier's documented effect, or reaches a pinned member other than
    through its name.  interfaces, if given, is a RomInterfaces: the callees'
    argument registers derived from their ROM code.
    """
    return _compare_compiles(real_assembly, stripped_assembly, preprocessed, symbol, declaration,
                            perturbed_assembly, interfaces)


def _compare_compiles(real_assembly, stripped_assembly, preprocessed, symbol, declaration,
                     perturbed_assembly=None, interfaces=None):
    """compare(), with the perturbation optional so tests can exercise the other rules"""
    size, pinned = pinned_members(declaration)
    from plausible import member_provenance, strip_comments_and_strings, whole_object_uses
    code = strip_comments_and_strings(preprocessed)
    for _, message in whole_object_uses(code, symbol) + member_provenance(
            code, {"symbol": symbol, "declaration": declaration}):
        raise SemanticError(f"after preprocessing: {message}")
    real, real_outside = parse_assembly(real_assembly)
    stripped, stripped_outside = parse_assembly(stripped_assembly)
    if sorted(real) != sorted(stripped):
        raise SemanticError("the real and stripped compiles define different functions")
    if normalised(real_outside) != normalised(stripped_outside):
        raise SemanticError("the real and stripped compiles differ outside their functions")
    names = set(real)
    for function in real.values():
        for mnemonic, operands, _ in function[0]:
            if mnemonic == "bl" and operands:
                names.add(operands[0])
    scope = file_scope(preprocessed)
    signatures = {name: function_signature(scope, name) for name in names}
    if perturbed_assembly is not None:
        _, mapping, _ = perturbed_declaration(declaration)
        perturbed, _ = parse_assembly(perturbed_assembly)
        if sorted(perturbed) != sorted(real):
            raise SemanticError("the real and layout-perturbed compiles define different functions")
        for name in sorted(real):
            perturbation_check(name, real[name], perturbed[name], signatures, symbol, size, pinned,
                               mapping, interfaces)
    # A pinned store may lack its read-modify-write load only for the
    # all-ones value, and only once the permuted compile has shown it follows
    # its member; without that compile the rule stays strict.
    return [(name,) + compare_function(name, real[name], stripped[name], signatures, symbol, size, pinned,
                                       interfaces, unloaded_all_ones=perturbed_assembly is not None)
            for name in sorted(real)]


def record(symbol, results, perturbed=False):
    """the report record for a passed semantic check"""
    parts = []
    for name, paths, read_modify_write, chained, *extra in results:
        unloaded, relied = (extra + [[], []])[:2]
        parts.append(f"`{name}` agrees on {paths} path{'s' if paths != 1 else ''}; "
                     f"read-modify-write loads at {list(n + 1 for n in read_modify_write)}, "
                     f"chained re-reads at {list(n + 1 for n in chained)}" +
                     # only what a verdict relied on beyond #94's rules, so
                     # reports that need neither keep their text
                     (f", unloaded all-ones stores at {list(n + 1 for n in unloaded)}" if unloaded else "") +
                     (f", callee interfaces from ROM: {'; '.join(relied)}" if relied else ""))
    return (f"* allowlisted volatile semantics: `{symbol}` stripped of volatile compiles to the same "
            f"behaviour{', and a compile with the pinned bytes moved follows every pinned access' if perturbed else ''}; " +
            "; ".join(parts))
