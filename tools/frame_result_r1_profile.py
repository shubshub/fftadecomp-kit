"""R1 holding an own-frame address at a frame-buffer owner's normal returns.

agbcc can leave the address of one of the owner's locals in R1 on a path that returns, as it leaves
them in R2/R3 (function_literal_exit_scratch_profile).  R1 is a result register under the ARM ABI:
the high word of a 64-bit result.  So unlike R2/R3 it is not dropped under the ABI premise; it is
dropped only when the ROM shows that no caller reads it:

* no four bytes of the ROM, at any offset, equal the function's address or its Thumb address (data
  tables and code included), and no halfword-aligned ROM word equals either one in a mirror of the
  cartridge ROM (the 16 MiB steps 0x09000000-0x0DFFFFFF: the wait-state 1 and 2 regions, and the
  upper half of each region, which a 16 MiB cartridge that leaves its top address line undecoded
  also mirrors).  So no image copied verbatim from ROM to IWRAM or EWRAM holds such a word either,
  whatever the alignment of the copy; and code executing there, or in the BIOS, cannot reach ROM by
  a direct branch (a Thumb BL reaches 4 MiB and an ARM B or BL 32 MiB), so it can reach the function
  only through a register;
* no Thumb B or B<cond> outside the function branches to its entry;
* the mapped function that ends at its entry has a closed control-flow graph, so nothing falls into it;
* every Thumb BL in the ROM that targets it lies in a mapped Thumb function and decodes as that BL there,
  and from the instruction after it, on every path, that caller writes R1 before any read, call or
  return (``dead_register.prove`` with ``dead_register.thumb_step``).  A call from the function to
  itself refuses.

What the scan cannot see is an address formed at run time (by arithmetic, in decompressed data, or a
mirror address assembled from bytes at an odd offset), and code run from VRAM or OAM, the only other
memory within a direct branch's reach of ROM.  So every report that uses the rule states the residual
premise ``PREMISE``.  The evidence (the scan, each
caller with its proof) is computed once per ROM, mapping and function, bound into the buffer
fingerprint with the dropped sites and stated on one ``* buffer frame result r1`` line.  Only the
frame-buffer owner's bound normal returns use it (``function_exit.aliases``); R0 keeps the refusal.
``POLICY`` gates it.
"""
import bisect
import hashlib
import json
import re
import struct

SCHEMA = "frame-result-r1-dead-at-callers-v1"
LINE = "* buffer frame result r1"
PREMISE = ("unproved runtime premise: code runs only from the BIOS, ROM, EWRAM and IWRAM, and no code reaches "
           "the function through an address formed at run time (by arithmetic, in decompressed data, or as a "
           "ROM mirror address assembled from bytes at an odd offset) rather than stored in the ROM, so its "
           "direct callers are all its callers")
MIRRORS = tuple(step * 0x01000000 for step in range(1, 6))     # 0x09000000-0x0DFFFFFF over 0x08000000
BRANCH_REACH = 4096
_CACHE = {}


class Policy:
    """The maintainer's switch."""

    def __init__(self):
        self.enabled = True


POLICY = Policy()


def _r1():
    import match
    return match.ARM_REG_R0 + 1


def _thumb_entries(proof):
    spans = []
    for entry in proof.entries:
        if entry.get("mode", "thumb") == "thumb":
            spans.append((int(entry["rom"], 16), int(entry["end"], 16)))
    return sorted(spans)


def _owner(spans, starts, site):
    index = bisect.bisect_right(starts, site) - 1
    if index >= 0 and spans[index][0] <= site < spans[index][1]:
        return spans[index]
    return None


def scan(rom, address):
    """(word hits, BL sites, B/B<cond> sites) naming ``address`` in the ROM image.

    Word hits are the function's address or Thumb address at any byte offset, and either one in a ROM
    mirror at a halfword-aligned offset."""
    import match
    base = match.ROM_BASE
    words = []
    values = [(value, 1) for value in (address, address | 1)]
    values += [(value + mirror, 2) for mirror in MIRRORS for value in (address, address | 1)]
    for value, alignment in values:
        packed = struct.pack("<I", value)
        start = 0
        while (found := rom.find(packed, start)) >= 0:
            if found % alignment == 0:
                words.append(base + found)
            start = found + 1
    calls = []
    for found in re.finditer(rb"(?=[\x00-\xff][\xf0-\xf7][\x00-\xff][\xf8-\xff])", rom, re.S):
        offset = found.start()
        if offset % 2:
            continue
        high, low = struct.unpack_from("<HH", rom, offset)
        displacement = ((high & 0x7FF) << 12) | ((low & 0x7FF) << 1)
        if displacement & 0x400000:
            displacement -= 0x800000
        if base + offset + 4 + displacement == address:
            calls.append(base + offset)
    branches = []
    first = max(0, (address - base - BRANCH_REACH) // 2 * 2)
    last = min(len(rom) - 2, address - base + BRANCH_REACH)
    for offset in range(first, last + 1, 2):
        (half,) = struct.unpack_from("<H", rom, offset)
        if half & 0xF800 == 0xE000:
            displacement = (half & 0x7FF) << 1
            if displacement & 0x800:
                displacement -= 0x1000
        elif half & 0xF000 == 0xD000 and (half >> 8) & 0xF < 0xE:
            displacement = (half & 0xFF) << 1
            if displacement & 0x100:
                displacement -= 0x200
        else:
            continue
        if base + offset + 4 + displacement == address:
            branches.append(base + offset)
    return sorted(set(words)), calls, branches


def evidence(proof, address, mapping):
    """The function's caller evidence; raises ValueError naming what the ROM does not show."""
    import dead_register
    import owner_admission_profile as owner
    raw = mapping if isinstance(mapping, (bytes, bytearray)) else str(mapping).encode()
    key = (hashlib.sha256(proof.rom).hexdigest(), hashlib.sha256(raw).hexdigest(), address)
    if key in _CACHE:
        kind, found = _CACHE[key]
        if kind == "refused":
            raise ValueError(found)
        return json.loads(found)
    try:
        spans = _thumb_entries(proof)
        starts = [start for start, _ in spans]
        own = _owner(spans, starts, address)
        if own is None or own[0] != address:
            raise ValueError("the function is not a mapped Thumb entry")
        words, sites, branches = scan(proof.rom, address)
        if words:
            raise ValueError(f"the ROM word at 0x{words[0]:08X} names the function")
        outside = [site for site in branches if not own[0] <= site < own[1]]
        if outside:
            raise ValueError(f"a Thumb branch at 0x{outside[0]:08X} reaches the function's entry")
        previous = _owner(spans, starts, address - 2)
        if previous is not None:
            try:
                closed = owner.refine(proof.span(previous[0]), previous[0], mapping)["cfg_closed"]
            except ValueError:
                closed = False
            if not closed:
                raise ValueError(f"the function before it, 0x{previous[0]:08X}, may fall into its entry")
        callers = []
        for site in sites:
            caller = _owner(spans, starts, site)
            if caller is None:
                raise ValueError(f"a BL at 0x{site:08X} outside every mapped Thumb function targets it")
            if caller[0] == address:
                raise ValueError(f"the function calls itself at 0x{site:08X}")
            data = proof.span(caller[0])
            item = dead_register.decode(data, caller[0], site)
            if item.size != 4 or item.mnemonic != "bl" or item.operands[0].imm != address:
                raise ValueError(f"0x{site:08X} in 0x{caller[0]:08X} does not decode as its BL")
            try:
                result = dead_register.prove(
                    site + 4, {_r1()}, dead_register.thumb_step(caller[0], data),
                    end="R1 is live at the end of a caller's path",
                    cycle="a caller has a path that never writes R1",
                    budget="the caller's R1 proof exceeds its state budget")
            except ValueError as error:
                raise ValueError(f"caller 0x{caller[0]:08X} after 0x{site:08X}: {error}") from None
            callers.append(dict(site=site, caller=caller[0], states=result.states,
                                body_sha256=dead_register.sha(data),
                                kills=sorted(node for node, _ in result.kills)))
        if not callers:
            raise ValueError("no direct caller")
        found = dict(schema=SCHEMA, function=address, callers=callers, words=0, branches=0,
                     previous=None if previous is None else previous[0], premise=PREMISE, premise_proved=False)
    except ValueError as error:
        _CACHE[key] = ("refused", str(error))
        raise
    _CACHE[key] = ("proved", json.dumps(found, sort_keys=True))
    return json.loads(_CACHE[key][1])


def project(proof, data, address, site, held, mapping):
    """Drop an own-frame R1 at the bound root's normal return when the callers' evidence holds."""
    import match
    r1 = _r1()
    root = getattr(proof, "_return_root", None)
    if not POLICY.enabled or root is None or proof.active or address != root[0] or data != root[1] or \
            site not in root[2] or r1 not in held:
        return held
    offset = held[r1]
    if type(offset) is not int or offset >= 0 or match.ARM_REG_R0 in held:
        return held
    try:
        proof._frame_r1_evidence = evidence(proof, address, mapping)
    except ValueError as error:
        raise ValueError(f"local stack pointer escapes through a return register (R1: {error})") from None
    proof._frame_r1_sites[site] = offset
    return {register: value for register, value in held.items() if register != r1}


def record(proof):
    sites = getattr(proof, "_frame_r1_sites", None)
    if not sites:
        proof.frame_result_r1 = None
        return
    proof.frame_result_r1 = dict(proof._frame_r1_evidence, sites=[[site, offset] for site, offset in sorted(sites.items())])


def lines(proof):
    found = getattr(proof, "frame_result_r1", None)
    if not found:
        return []
    sites = ", ".join(f"`0x{site:08X} r1 {offset:+d}`" for site, offset in found["sites"])
    callers = ", ".join(f"0x{row['site']:08X} in 0x{row['caller']:08X} (R1 written at "
                        + " ".join(f"0x{node:08X}" for node in row["kills"]) + f"; {row['states']} states)"
                        for row in found["callers"])
    return [f"{LINE}: `{found['schema']}` own-frame addresses dropped at the owner's normal returns: {sites}; "
            f"no ROM word at any byte offset equals 0x{found['function']:08X} or 0x{found['function'] | 1:08X} "
            f"and no halfword-aligned one equals either in a ROM mirror (0x09000000-0x0DFFFFFF), "
            f"no Thumb branch outside it reaches its entry and nothing falls into it; every direct caller writes "
            f"R1 before any read, call or return: {callers}; {found['premise']}"]


def fingerprint_payload(proof):
    found = getattr(proof, "frame_result_r1", None)
    if not found:
        return None
    return json.dumps(["frame-result-r1-v1", found], sort_keys=True, separators=(",", ":")).encode()
