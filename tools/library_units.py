"""Library units: ROM ranges the original build compiled with another toolchain.

Some library objects in the ROM were prebuilt with settings other than the
game's `agbcc -mthumb-interwork -O2`.  A decomp records each such object as a
row of `config/library_units.json`; the range is a ROM fact, so the table
lives with the decomp, next to `config/data_symbols.json`.  The kit owns the
closed set of toolchains a row may name and every check:

* a row names one toolchain from TOOLCHAINS, a range of at least two index
  functions whose ends are index function boundaries and that no index
  function straddles, ROM identity bytes (a whole NUL-terminated string of at
  least 8 characters or a digest of at least 16 bytes) that are re-read from
  the ROM and that no other row uses, and a proving function inside it;
* rows never overlap;
* a function inside a unit is verified with the unit's toolchain, or with
  the default toolchain only when the unit's toolchain emits the identical
  relocatable function (consistency);
* a unit toolchain is never admitted outside its unit, and no other
  non-default toolchain is admitted at all, except the older explicit
  fixed-O0 orphan-constant selector, outside every unit or inside an
  agbcc-O0-v1 unit;
* the proving function is verified with the unit's toolchain and does not
  compile to the same function under the default toolchain (necessity); a
  row whose proof fails either way is reported as stale.

A unit report binds the canonical row, the toolchain id and the SHA-256 of
the compiler binary that produced it.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import struct
import subprocess
import tempfile

import m4a_track_switch as music
from refusal import Refusal

TABLE = Path("config") / "library_units.json"
ROM_BASE = 0x08000000

# The closed set.  `old` toolchains must be pret/agbcc's -DOLD_COMPILER build:
# that compiler rejects the new compiler's -fprologue-bugfix option.
TOOLCHAINS = {
    "agbcc-O0-v1": {"cc": "$HOME/agbcc/gcc/agbcc", "flags": "-mthumb-interwork -O0", "old": False},
    "agbcc-O1-v1": {"cc": "$HOME/agbcc/gcc/agbcc", "flags": "-mthumb-interwork -O1", "old": False},
    "old-agbcc-O2-v1": {"cc": "$HOME/agbcc/gcc/old_agbcc", "flags": "-mthumb-interwork -O2", "old": True},
}
KEYS = {"name", "start", "end", "toolchain", "identity", "proof", "evidence"}
MIN_IDENTITY_TEXT = 8
MIN_IDENTITY_BYTES = 16
MIN_FUNCTIONS = 2
# the explicit fixed-O0 orphan-constant selector compiles with these flags too
O0_TOOLCHAIN = "agbcc-O0-v1"

UNIT_LINE = "* library unit: "
TOOLCHAIN_LINE = "* unit toolchain: "
COMPILER_LINE = "* unit compiler SHA-256: "
ORPHAN_LINE = "* unit orphan constants: "
MARKERS = ("* library unit", "* unit ")


class Unit:
    def __init__(self, row, text):
        self.row = row
        self.text = text
        self.name = row["name"]
        self.start = int(row["start"], 16)
        self.end = int(row["end"], 16)
        self.toolchain = row["toolchain"]
        self.proof = int(row["proof"], 16)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def snapshot(root):
    try:
        return (Path(root) / TABLE).read_bytes()
    except FileNotFoundError:
        return None


def _address(value, what):
    if type(value) is not str or re.fullmatch(r"0x[0-9A-F]{8}", value) is None:
        raise Refusal(f"library unit {what} must be canonical 0x%08X text")
    return int(value, 16)


def _text(value, what, limit):
    if type(value) is not str or not 0 < len(value) <= limit or \
            any(not " " <= character <= "~" for character in value):
        raise Refusal(f"library unit {what} must be printable ASCII of 1..{limit} characters")
    return value


def parse(raw, rom, mapping):
    """The validated rows of a table snapshot; () when there is no table."""
    if raw is None:
        return ()

    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise Refusal("duplicate key in the library unit table")
            result[key] = value
        return result

    try:
        document = json.loads(raw, object_pairs_hook=unique)
        entries = json.loads(mapping)
    except (TypeError, ValueError) as error:
        raise Refusal(f"library unit table or function index is not valid JSON: {error}") from None
    if type(document) is not dict or set(document) != {"units"} or type(document["units"]) is not list:
        raise Refusal("library unit table must be an object holding one `units` list")
    if type(entries) is not list:
        raise Refusal("function index must be a list")
    spans = []
    for entry in entries:
        try:
            spans.append((int(entry["rom"], 16) & ~1, int(entry["end"], 16), entry["mode"]))
        except (TypeError, ValueError, KeyError):
            raise Refusal("malformed function index entry") from None
    units, names, claimed = [], set(), []
    for row in document["units"]:
        if type(row) is not dict or set(row) != KEYS:
            raise Refusal(f"library unit row must have exactly the keys {sorted(KEYS)}")
        name = _text(row["name"], "name", 80)
        if name in names:
            raise Refusal(f"duplicate library unit name {name}")
        names.add(name)
        _text(row["evidence"], "evidence", 2000)
        start, end = _address(row["start"], "start"), _address(row["end"], "end")
        proof = _address(row["proof"], "proof")
        if not ROM_BASE <= start < end <= ROM_BASE + len(rom) or start % 2 or end % 2:
            raise Refusal(f"library unit {name} must be an even, nonempty ROM range")
        if row["toolchain"] not in TOOLCHAINS:
            raise Refusal(f"library unit {name} names unknown toolchain {row['toolchain']!r}")
        identity = row["identity"]
        if type(identity) is not list or not identity:
            raise Refusal(f"library unit {name} needs ROM identity evidence")
        spans_used = []
        for item in identity:
            if type(item) is not dict:
                raise Refusal(f"library unit {name} identity items must be objects")
            where = _address(item.get("address"), "identity address") - ROM_BASE
            if set(item) == {"address", "ascii"}:
                expected = _text(item["ascii"], "identity string", 64).encode("ascii")
                if len(expected) < MIN_IDENTITY_TEXT:
                    raise Refusal(f"library unit {name}: an identity string needs at least "
                                  f"{MIN_IDENTITY_TEXT} characters")
                if not 0 <= where <= len(rom) - len(expected) - 1 or \
                        rom[where:where + len(expected) + 1] != expected + b"\0":
                    raise Refusal(f"library unit {name}: identity string {item['ascii']!r} "
                                  f"is not a NUL-terminated string at {item['address']} in this ROM")
                if where and 0x20 <= rom[where - 1] <= 0x7E:
                    raise Refusal(f"library unit {name}: identity string {item['ascii']!r} "
                                  f"is the tail of a longer string")
                spans_used.append((where, where + len(expected) + 1))
            elif set(item) == {"address", "size", "sha256"}:
                size, digest = item["size"], item["sha256"]
                if type(size) is not int or not MIN_IDENTITY_BYTES <= size <= 0x100000 or type(digest) is not str or \
                        re.fullmatch(r"[0-9a-f]{64}", digest) is None:
                    raise Refusal(f"library unit {name}: malformed identity digest")
                if not 0 <= where <= len(rom) - size or sha(rom[where:where + size]) != digest:
                    raise Refusal(f"library unit {name}: identity digest of {size} bytes "
                                  f"at {item['address']} differs from this ROM")
                spans_used.append((where, where + size))
            else:
                raise Refusal(f"library unit {name} identity items are {{address, ascii}} "
                              f"or {{address, size, sha256}}")
        for lo, hi in spans_used:
            for other, other_lo, other_hi in claimed:
                if lo < other_hi and other_lo < hi:
                    raise Refusal(f"library units {other} and {name} share identity bytes")
        claimed.extend((name, lo, hi) for lo, hi in spans_used)
        inside = [span for span in spans if start <= span[0] and span[1] <= end]
        for lo, hi, _ in spans:
            if lo < end and start < hi and not (start <= lo and hi <= end):
                raise Refusal(f"library unit {name} straddles index function 0x{lo:08X}")
        if not any(lo == start for lo, _, _ in inside) or not any(hi == end for _, hi, _ in inside):
            raise Refusal(f"library unit {name} must start and end on index function boundaries")
        if any(mode != "thumb" for _, _, mode in inside):
            raise Refusal(f"library unit {name} covers a non-Thumb index function")
        if len({lo for lo, _, _ in inside}) < MIN_FUNCTIONS:
            raise Refusal(f"library unit {name} must cover a whole library object of at least "
                          f"{MIN_FUNCTIONS} index functions, not one function")
        if not any(lo == proof for lo, _, _ in inside):
            raise Refusal(f"library unit {name}: proof {row['proof']} is not an index function in the unit")
        units.append(Unit(row, canonical(row)))
    units.sort(key=lambda unit: unit.start)
    for before, after in zip(units, units[1:]):
        if after.start < before.end:
            raise Refusal(f"library units {before.name} and {after.name} overlap")
    return tuple(units)


_loaded = {}


def load(root):
    """The validated rows of a decomp's table; () when it has none.

    Every report validation asks, so the result is kept per table, index and
    ROM file state (path, inode, size, modification time)."""
    raw = snapshot(root)
    if raw is None:
        return ()
    from rompath import rom_path
    try:
        path = rom_path(root)
    except SystemExit as error:
        raise Refusal(f"library units need the ROM: {error}") from None
    try:
        mapping = (Path(root) / "config" / "functions.json").read_bytes()
    except FileNotFoundError:
        raise Refusal("library units need config/functions.json") from None
    state = os.stat(path)
    key = (sha(raw), sha(mapping), os.path.realpath(path), state.st_ino, state.st_size, state.st_mtime_ns)
    if key not in _loaded:
        if len(_loaded) > 8:
            _loaded.clear()
        _loaded[key] = parse(raw, Path(path).read_bytes(), mapping)
    return _loaded[key]


def containing(units, address, end=None):
    """The unit holding [address, end), None outside every unit."""
    end = address + 1 if end is None else end
    for unit in units:
        if unit.start <= address and end <= unit.end:
            return unit
        if address < unit.end and unit.start < end:
            raise Refusal(f"0x{address:08X} straddles library unit {unit.name}")
    return None


_identities = {}


def resolve(toolchain):
    """The compiler, flags and compiler-binary SHA-256 of one closed-set toolchain."""
    if toolchain not in TOOLCHAINS:
        raise Refusal(f"unknown library unit toolchain {toolchain!r}")
    spec = TOOLCHAINS[toolchain]
    expanded = os.path.expandvars(spec["cc"])
    path = shutil.which(expanded) or expanded
    try:
        digest = sha(Path(path).read_bytes())
    except OSError:
        raise Refusal(f"toolchain {toolchain} needs {spec['cc']}") from None
    if spec["old"]:
        key = (path, digest)
        if key not in _identities:
            _identities[key] = _rejects_new_option(path)
        if not _identities[key]:
            raise Refusal(f"{spec['cc']} accepts -fprologue-bugfix, so it is not the OLD_COMPILER build "
                          "(rebuild it from a clean tree with `make -C gcc old`)")
    return {"id": toolchain, "cc": spec["cc"], "flags": spec["flags"], "sha256": digest}


def _rejects_new_option(path):
    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "probe.i"
        source.write_text("int probe;\n")
        result = subprocess.run([path, "-fprologue-bugfix", str(source), "-o",
                                 str(Path(directory) / "probe.s")],
                                stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=60)
    # the new compiler accepts the option and exits 0; the old one names it and fails
    return result.returncode != 0 and "prologue-bugfix" in result.stderr


def schemas(unit=None, address=None, orphan=None):
    """Byte-level schemas admitted for this library unit and caller."""
    import match_evidence as evidence
    import lshrdi3_profile
    import unit_float_multiply_profile as multiply
    admitted = {evidence.SCHEMA, evidence.FRAMED_SCHEMA, evidence.LINKED_SCHEMA,
                evidence.FRAMED_LINKED_SCHEMA, evidence.DATA_SCHEMA, evidence.FRAMED_DATA_SCHEMA,
                evidence.FUNCTION_ADDRESS_SCHEMA, evidence.FRAMED_FUNCTION_ADDRESS_SCHEMA}
    if address == 0x08141C78:
        import flash_sized_verify
        if flash_sized_verify.unit_owner(unit, address, orphan):
            admitted.add(flash_sized_verify.SCHEMA)
    if address == 0x08141BE0:
        import flash_sector_verify
        if flash_sector_verify.unit_owner(unit, address, orphan):
            admitted.add(flash_sector_verify.SCHEMA)
    if address == 0x08141AB0:
        import flash_reader_install
        if flash_reader_install.unit_owner(unit, address, orphan):
            admitted.add(flash_reader_install.SCHEMA)
    if address == 0x08142160:
        import flash_sector_programmer
        if flash_sector_programmer.unit_owner(unit, address, orphan):
            admitted.add(flash_sector_programmer.SCHEMA)
    if address == 0x08141EB8:
        import flash_chip_erase
        if flash_chip_erase.unit_owner(unit, address, orphan):
            admitted.add(flash_chip_erase.SCHEMA)
    if address == 0x08141F2C:
        import flash_sector_erase
        if flash_sector_erase.unit_owner(unit, address, orphan):
            admitted.add(flash_sector_erase.SCHEMA)
    if lshrdi3_profile.unit_owner(unit, address, orphan):
        admitted.add(lshrdi3_profile.UNIT_SCHEMA)
    if music.unit_owner(unit, address, orphan):
        admitted.add(music.SCHEMA)
    import unit_double_multiply as double_mul
    if double_mul.unit_owner(unit, address, orphan):
        admitted.add(double_mul.SCHEMA)
    import unit_double_add_parts as add_parts
    if add_parts.unit_owner(unit, address, orphan):
        admitted.add(add_parts.SCHEMA)
    import unit_double_constructor as constructor
    if constructor.unit_owner(unit, address, orphan):
        admitted.add(constructor.SCHEMA)
    if multiply.unit_owner(unit, address, orphan):
        admitted.add(multiply.SCHEMA)
    return frozenset(admitted)


def _selectors(args):
    names = ("signed_quotient_profile", "unsigned_quotient_profile", "signed_runtime_profile",
             "unsigned_runtime_profile", "addressed_signed_runtime_profile", "software_double_profile",
             "software_double_remainder_profile", "function_address_profile", "switch_profile",
             "switch_data_profile", "owner_runtime_profile", "palette_closure_bundle")
    return [name for name in names if getattr(args, name, None)]


def gate(root, address, args):
    """Admit this run's toolchain for the address, or refuse.

    Returns None for the default toolchain outside every unit,
    {consistent, source} for the default toolchain inside a unit whose
    toolchain emits the identical function (the caller must verify that same
    source), "exploratory" for another toolchain on the ordinary path outside
    every unit (never a match), or the unit context {unit, tool} for
    --unit-toolchain.  May set args.cc and args.flags to the unit's toolchain.
    """
    import match
    from compiler_orphan_constants_native_profile import SELECTOR as O0_SELECTOR
    defaults = (match.DEFAULT_CC, match.DEFAULT_CPP, match.DEFAULT_AS, match.DEFAULT_OBJCOPY,
                match.DEFAULT_LD, match.DEFAULT_FLAGS)
    chosen = (args.cc, args.cpp, args.assembler, args.objcopy, args.linker, args.flags)
    units = load(root)
    unit = None
    if units:
        try:
            span = match.function_span(address, os.path.join(root, "symbols", "functions.txt"))
        except OSError:
            span = None
        unit = containing(units, address, address + span if span and span > 0 else None)
    requested = getattr(args, "unit_toolchain", None)
    selectors = _selectors(args)
    engine_tracks = getattr(args, "switch_data_profile", None) == music.SELECTOR
    if engine_tracks and (requested != music.TOOLCHAIN or not music.unit_owner(unit, address) or
                          selectors != ["switch_data_profile"]):
        raise Refusal("m4a engine tracks require the isolated fixed old-agbcc unit and indexed owner")
    if requested:
        if chosen != defaults:
            raise Refusal("--unit-toolchain fixes the compiler and flags; do not combine it with toolchain options")
        if (selectors and not engine_tracks) or args.mode != "thumb" or args.control_flow_profile != "ordinary" or \
                getattr(args, "wsl", "Ubuntu") != "Ubuntu" or \
                getattr(args, "wsl_path", match.DEFAULT_WSL_PATH) != match.DEFAULT_WSL_PATH:
            raise Refusal("library unit toolchains are admitted on the ordinary Thumb path only, "
                          "with the default WSL options")
        if unit is None:
            raise Refusal(f"0x{address:08X} is not inside a library unit; --unit-toolchain is admitted only there")
        if unit.toolchain != requested:
            raise Refusal(f"0x{address:08X} lies in library unit {unit.name}, built with "
                          f"{unit.toolchain}, not {requested}")
        tool = resolve(unit.toolchain)
        args.cc, args.flags = tool["cc"], tool["flags"]
        return {"unit": unit, "tool": tool}
    if chosen != defaults:
        if getattr(args, "owner_runtime_profile", None) == O0_SELECTOR and \
                (unit is None or unit.toolchain == O0_TOOLCHAIN):
            return None
        if unit is not None:
            raise Refusal(f"0x{address:08X} lies in library unit {unit.name}: verify it with "
                          f"--unit-toolchain {unit.toolchain} and no other toolchain option")
        if _selectors(args):
            raise Refusal("a non-default toolchain is admitted only through --unit-toolchain inside a library unit")
        return "exploratory"
    if unit is not None:
        import match_evidence as evidence
        source = evidence.source_fingerprint(root, address)
        try:
            same = consistent(root, address, unit)
        except (RuntimeError, OSError, subprocess.SubprocessError) as error:
            raise Refusal(f"0x{address:08X} lies in library unit {unit.name}: the consistency check "
                          f"could not compile it: {error}") from None
        if not same:
            raise Refusal(f"0x{address:08X} lies in library unit {unit.name}: its default-toolchain object "
                          f"differs from {unit.toolchain}'s; verify it with --unit-toolchain {unit.toolchain}")
        return {"consistent": unit, "source": source}
    return None


def recheck(root, context):
    """Refuse when the table row or the compiler binary changed during the run."""
    unit = containing(load(root), context["unit"].start)
    if unit is None or unit.text != context["unit"].text or \
            resolve(unit.toolchain)["sha256"] != context["tool"]["sha256"]:
        raise Refusal("library unit table, ROM or unit compiler changed during verification; re-run match.py")


def signature(image, address):
    """What fixes the linked function: .text, its relocations and the function symbol."""
    import match
    symbol, offset = match.function_record(image, f"func_{address:08X}", address, True)
    names = image["section_names"]
    for index, section in enumerate(image["sections"]):
        if section[2] & 2 and section[5] and index != image["text_index"] and names[index] != ".rodata":
            raise Refusal(f"consistency check refuses nonempty allocated section {names[index]}")
    relocations = []
    for index in image["relocations"]:
        section = image["sections"][index]
        if section[7] != image["text_index"]:
            continue
        if section[1] != 9:
            raise Refusal("consistency check requires REL relocations")
        symbols = image["symbol_tables"][section[6]]
        payload = image["section_data"][index]
        for position in range(0, len(payload), 8):
            site, info = struct.unpack_from("<II", payload, position)
            target = symbols[info >> 8]
            own = target["name"] == f"func_{address:08X}" and target["section"] == image["text_index"]
            if not own and (target["section"] != 0 or not target["name"]):
                raise Refusal("consistency check requires relocations to named external symbols")
            relocations.append((site, info & 255, target["name"]))
    return image["text"], tuple(sorted(relocations)), offset, symbol["value"], symbol["size"]


def compiled_signature(root, address, cc, flags):
    import match
    sources = sorted(Path(root, "src").rglob(f"{address:08X}.c"))
    if len(sources) != 1:
        raise Refusal(f"0x{address:08X} needs exactly one source")
    args = argparse.Namespace(cc=cc, cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=flags)
    runner = match.Runner(cc, "Ubuntu", match.DEFAULT_WSL_PATH, root=str(root))
    with runner.workspace() as workspace:
        _, _, image = match.compile_object(runner, workspace, args, root, address,
                                           sources[0].relative_to(root).as_posix())
    return signature(image, address)


def consistent(root, address, unit):
    """True when the unit's toolchain emits the default toolchain's function."""
    import match
    import match_evidence as evidence
    before = evidence.source_fingerprint(root, address)
    tool = resolve(unit.toolchain)
    default = compiled_signature(root, address, match.DEFAULT_CC, match.DEFAULT_FLAGS)
    other = compiled_signature(root, address, tool["cc"], tool["flags"])
    if evidence.source_fingerprint(root, address) != before:
        raise Refusal("source changed during the library unit consistency check")
    return default == other


def necessary(root, unit):
    """True when the proving function's default-toolchain function differs from the unit's."""
    import match
    tool = resolve(unit.toolchain)
    other = compiled_signature(root, unit.proof, tool["cc"], tool["flags"])
    try:
        default = compiled_signature(root, unit.proof, match.DEFAULT_CC, match.DEFAULT_FLAGS)
    except (RuntimeError, ValueError):
        return True
    return default != other


def exclude_orphan_constants(runner, workspace, args, original_elf, address, rom, mapping, objects, index):
    """Drop an authenticated compiler-orphan .rodata from a unit-toolchain object.

    agbcc below -O2 also emits each literal-pool word into .rodata, where
    nothing references it.  The existing orphan prerequisite authenticates the
    original object (every word duplicates a reached in-function literal with
    the same symbol and addend, and nothing refers to the section).  The two
    sections are then removed and the result must keep the identical .text,
    .text relocations and function symbol.  The excluded bytes earn no credit.
    """
    import match
    import compiler_orphan_constants_prerequisite as prerequisite
    image = match.elf_image(original_elf)
    extra = [index_ for index_, section in enumerate(image["sections"])
             if section[2] & 2 and section[5] and index_ != image["text_index"]]
    if not extra:
        return original_elf, image["text"], image, None
    preprocessed = runner.read_binary(f"{workspace}/f.i")
    inventory = prerequisite.verify(original_elf, address, objects if objects is not None else b"{}",
                                    preprocessed, selector=prerequisite.SELECTOR, mapping=mapping,
                                    index=index, rom=rom)
    quoted = shlex.quote(workspace)
    runner.sh(f"{args.objcopy} --remove-section=.rodata --remove-section=.rel.rodata {quoted}/f.o")
    runner.sh(f"{args.objcopy} -O binary --only-section=.text {quoted}/f.o {quoted}/f.bin")
    stripped = runner.read_binary(f"{workspace}/f.o")
    result = match.elf_image(stripped)
    if runner.read_binary(f"{workspace}/f.bin") != result["text"]:
        raise Refusal("objcopy output does not equal the excluded object's .text")
    if signature(result, address) != signature(image, address) or \
            ".rodata" in result["section_names"] or ".rel.rodata" in result["section_names"]:
        raise Refusal("orphan exclusion changed the function or kept the orphan section")
    # the prerequisite itself never excludes; this wrapper just did
    inventory = dict(inventory, section_exclusion_performed=True)
    return stripped, result["text"], result, {
        "prerequisite": inventory, "excluded_sections": [".rodata", ".rel.rodata"],
        "section_exclusion_performed": True, "original_elf_sha256": sha(original_elf),
        "excluded_elf_sha256": sha(stripped), "excluded_ROM_credit": 0}


def report_lines(context, orphan):
    lines = [f"{UNIT_LINE}`{context['unit'].text}`", f"{TOOLCHAIN_LINE}`{context['tool']['id']}`",
             f"{COMPILER_LINE}`{context['tool']['sha256']}`"]
    if orphan is not None:
        lines.append(f"{ORPHAN_LINE}`{canonical(orphan)}`")
    return lines


def binding(report):
    """(row, toolchain, compiler SHA-256, orphan) bound by a unit report; None for any other."""
    lines = [line for line in report.splitlines() if line.lstrip().startswith(MARKERS)]
    if not lines:
        return None

    def value(prefix, required=True):
        found = [line for line in lines if line.startswith(prefix)]
        if len(found) > 1 or required and not found:
            raise Refusal("missing or duplicate library unit report line")
        if not found:
            return None
        text = found[0][len(prefix):]
        if len(text) < 2 or text[0] != "`" or text[-1] != "`":
            raise Refusal("malformed library unit report line")
        return text[1:-1]

    result = (value(UNIT_LINE), value(TOOLCHAIN_LINE), value(COMPILER_LINE), value(ORPHAN_LINE, False))
    if len(lines) != 3 + (result[3] is not None):
        raise Refusal("unknown library unit report line")
    return result


def report_toolchain(report):
    bound = binding(report)
    return None if bound is None else bound[1]


def report_arguments(report):
    """The compiler configuration a unit report was produced with; None for any other report."""
    import match
    toolchain = report_toolchain(report)
    if toolchain is None:
        return None
    tool = resolve(toolchain)
    return argparse.Namespace(cc=tool["cc"], cpp=match.DEFAULT_CPP, assembler=match.DEFAULT_AS,
                              objcopy=match.DEFAULT_OBJCOPY, linker=match.DEFAULT_LD, flags=tool["flags"],
                              owner_runtime_profile=None)


def report_admitted(report, root, address):
    """The library unit rule for one saved report."""
    import match
    from compiler_orphan_constants_native_profile import SCHEMA as O0_SCHEMA
    try:
        units = load(root)
        unit = containing(units, address)
        bound = binding(report)
        lines = report.splitlines()
        compilers = [line for line in lines if line.startswith("* compiler: ")]
        verifications = [line for line in lines if line.startswith("* verification: ")]
        if bound is not None:
            row, toolchain, digest, orphan = bound
            if orphan is not None:
                json.loads(orphan)
            tool = resolve(toolchain)
            return (unit is not None and row == unit.text and toolchain == unit.toolchain and
                    digest == tool["sha256"] and compilers == [f"* compiler: `{tool['cc']} {tool['flags']}`"] and
                    len(verifications) == 1 and
                    verifications[0] in [f"* verification: `{schema}`" for schema in schemas(unit, address, orphan)])
        if verifications == [f"* verification: `{music.SCHEMA}`"]:
            return False
        if verifications == [f"* verification: `{O0_SCHEMA}`"]:
            return unit is None or unit.toolchain == O0_TOOLCHAIN
        if compilers not in ([], [f"* compiler: `{match.DEFAULT_CC} {match.DEFAULT_FLAGS}`"]):
            return False
        return unit is None or consistent(root, address, unit)
    except (OSError, ValueError, KeyError, TypeError, RuntimeError, subprocess.SubprocessError):
        return False


def status_summary(root, functions, matched, code_end):
    """Per-unit counts and the proof/staleness problems of the table, for status.py."""
    problems = []
    try:
        units = load(root)
    except (OSError, ValueError, TypeError, KeyError) as error:
        return [f"library units: {error}"], None
    if not units:
        return [], None
    spans = [(int(entry["rom"], 16) & ~1, int(entry["end"], 16)) for entry in functions
             if int(entry["rom"], 16) < code_end]
    rows = []
    outside = [0, 0]
    inside_any = set()
    for unit in units:
        members = [span for span in spans if unit.start <= span[0] and span[1] <= unit.end]
        inside_any.update(start for start, _ in members)
        done = [span for span in members if span[0] in matched]
        rows.append({"name": unit.name, "start": unit.start, "end": unit.end, "toolchain": unit.toolchain,
                     "functions": len(members), "matched": len(done),
                     "bytes": sum(end - start for start, end in members),
                     "matched_bytes": sum(end - start for start, end in done)})
        label = f"library unit {unit.name}"
        if unit.proof not in matched:
            problems.append(f"{label}: proving function 0x{unit.proof:08X} is not verified")
            continue
        try:
            report = (Path(root) / "docs" / "match" / f"{unit.proof:08X}.md").read_text(encoding="utf-8")
            bound = binding(report)
            if bound is None or bound[0] != unit.text:
                problems.append(f"{label}: proving function 0x{unit.proof:08X} is not verified "
                                f"with {unit.toolchain}")
            elif not necessary(root, unit):
                problems.append(f"{label} is stale: proving function 0x{unit.proof:08X} compiles to the "
                                f"same function under the default toolchain")
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            problems.append(f"{label}: {error}")
    for start, _ in spans:
        if start not in inside_any:
            outside[0] += 1
            outside[1] += start in matched
    return problems, {"units": rows, "outside_functions": outside[0], "outside_matched": outside[1]}
