"""A compiler read-only initialiser bound to the ROM bytes its literals address (default path).

agbcc lowers a local aggregate with a constant initialiser, `u16 ticks[4] = {58, 82, 270, 270};`, to a
`.rodata` object plus an inline copy (ldm/stm, or word loads and stores) or a call to the compiler's `memcpy`.
The default path linked `.text` only and refused any other allocated section ("unexpected nonempty allocated
section"), so such a function was admitted only under the ROM-table-copy and stack-index selectors, which bind
the same section (rom_table_copy_profile).  This profile binds it on the default path, for the data-buffer
schemas, with the selector's own helpers:

1. the object has exactly one allocated section besides `.text`: a plain `.rodata` (PROGBITS, flags A only,
   alignment 1, 2 or 4, 1 to 4096 bytes) that carries no relocations of its own;
2. every reference to it is an R_ARM_ABS32 relocation in `.text` against its local section symbol, covering a
   complete, aligned literal word of the function that no other relocation touches, with its addend inside
   the section;
3. every such word in the ROM, less its addend, gives the same base B; B is aligned to the section, and
   [B, B + size) lies inside the cartridge ROM image (not RAM, IWRAM or a ROM mirror, and not past the image's
   end) and outside the owner;
4. the ROM bytes at [B, B + size) equal the section bytes;
5. the link places `.rodata` at B: the linked section has exactly that address, size and those bytes, and
   each literal word links to B plus its addend (the full byte comparison covers those words too);
6. on every default route, plain routes included, with or without a `.rodata` initialiser (a struct
   assignment calls it too), a call to the unique undefined global `memcpy` is a call to the pinned copy
   helper func_081443FC, whose 98 bytes must be the canonical copy routine's (COPY_SHA256) and which must
   be an indexed Thumb function; the walks then treat it as any call to that helper
   (copy_helper_summary_profile's summary under its own preconditions, or an ordinary walked callee);
7. the data-buffer proof types each literal word as the bound initialiser (its manifest records the binding,
   the proof fingerprint covers it, and a report line prints B, the size and the bytes' SHA-256); a `.rodata`
   binding whose function is not admitted by a data-buffer schema refuses (the `memcpy` binding alone has no
   such gate).

The binding is byte equality: the linked function equals the ROM function, literal words included, and the
bytes at B equal the compiler's initialiser, so the ROM function reads the constants the C initialiser gives.
Nothing more is proved about accesses through the literal (reads, writes, calls, escapes): as for every named
data object, the walks treat it as an untracked pointer, under the buffer walk's standing premise, and its
extent is not walked.  Writes through it and escapes of its address are not refused, although the object is
read-only in the ROM.
"""
import hashlib
import struct

POLICY = "readonly-initializer-v1"
MANIFEST_KEY = "readonly_initializer"
LINE = "* read-only initialiser"
# What the binding does not walk: every access through the literal (read, write, call, escape) gets a
# named object's treatment; writes and escapes are not refused here.
EXTENT = ("accesses through the literal (reads, writes, calls, escapes) get a named object's treatment, "
          "extent not walked")
ROM_BASE = 0x08000000
HELPER = 0x081443FC
HELPER_SIZE = 98


def opted_in(binding):
    """The default route passes an empty dict to collect the binding; None keeps .text only."""
    if binding is None:
        return False
    if type(binding) is not dict or binding:
        raise ValueError("read-only initialiser binding requires an empty collection")
    return True


def section(image, allocated_text_only):
    """The object's plain .rodata section (index, bytes, alignment), or None for a .text-only object.

    Any other allocated section, or a second one, keeps the .text-only refusal."""
    import rom_table_copy_profile as rom_copy
    extra = [index for index, item in enumerate(image["sections"])
             if item[2] & 2 and item[5] and index != image["text_index"]]
    if len(extra) != 1 or image["section_names"][extra[0]] != ".rodata":
        allocated_text_only(image)
        return None
    found = rom_copy.rodata_section(image)
    text_section = image["sections"][image["text_index"]]
    if text_section[1] != 1 or text_section[2] & 7 != 6:
        raise ValueError("expected read-only executable .text")
    return found


def site(rodata, target_symbol, image, relocation, function_size, address, occupied):
    """The addend of one literal word that addresses the initialiser, or None for any other relocation."""
    if rodata is None or target_symbol["section"] != rodata[0]:
        return None
    if target_symbol["type"] != 3 or target_symbol["bind"] != 0 or target_symbol["value"] or target_symbol["name"]:
        raise ValueError("read-only initialiser relocation must name its local section symbol")
    if relocation < 0 or (address + relocation) % 4 or relocation + 4 > function_size:
        raise ValueError("read-only initialiser relocation must cover an aligned complete literal word")
    positions = set(range(relocation, relocation + 4))
    if positions & occupied:
        raise ValueError("overlapping read-only initialiser, data or call relocations")
    occupied.update(positions)
    addend = struct.unpack_from("<I", image["text"], relocation)[0]
    if addend >= len(rodata[1]):
        raise ValueError("read-only initialiser literal addend outside the initialiser")
    return addend


def memcpy_target(image, target_symbol, rom):
    """The pinned copy helper, for the compiler's undefined `memcpy`."""
    import rom_table_copy_profile as rom_copy
    from local_rom_halfword_table_profile import COPY_SHA256
    target = rom_copy.memcpy_target(image, target_symbol)
    body = rom[HELPER - ROM_BASE:HELPER - ROM_BASE + HELPER_SIZE]
    if target != HELPER or len(body) != HELPER_SIZE or hashlib.sha256(body).hexdigest() != COPY_SHA256:
        raise ValueError("compiler memcpy requires the canonical pinned copy helper at 0x081443FC")
    return HELPER


def bind(image, address, rom, sites, collection):
    """Bind the initialiser to the ROM bytes at the single base its literal words agree on."""
    import rom_table_copy_profile as rom_copy
    binding = rom_copy.rodata_binding(image, address, rom)
    if binding["sites"] != sorted([offset, addend] for offset, addend in sites.items()):
        raise ValueError("read-only initialiser sites differ from the owner's literal relocations")
    collection.update(binding)
    return collection


def linker_line(binding):
    return f".rodata 0x{binding['base']:08X} : {{ *(.rodata) }} "


def check_linked(linked, binding, rom, patched):
    """The linked image carries exactly the bound initialiser, and each literal word links to it."""
    import rom_table_copy_profile as rom_copy
    rom_copy.check_linked_rodata(linked, binding, rom)
    for offset, addend in binding["sites"]:
        if struct.unpack_from("<I", linked["text"], offset)[0] != binding["base"] + addend:
            raise ValueError("linked read-only initialiser word does not equal its bound address")
        patched.update(range(offset, offset + 4))


def manifest_record(binding):
    return dict(base=binding["base"], size=binding["size"], sha256=binding["sha256"],
                sites=[list(item) for item in binding["sites"]])


def report_line(record):
    sites = ", ".join(f"+0x{offset:X}" + (f" (+{addend})" if addend else "") for offset, addend in record["sites"])
    return (f"{LINE}: `.rodata` {record['size']} bytes at 0x{record['base']:08X}, SHA-256 `{record['sha256']}`, "
            f"addressed by the owner's literal words at {sites}; {EXTENT}")
