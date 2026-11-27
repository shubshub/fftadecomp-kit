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
* no Thumb B or B<cond> outside the function branches to its entry, and no ADR forms its address (the
  Thumb ``add rd, pc, #imm``, and ARM ADD/SUB immediates with Rn = PC);
* nothing falls into the entry: the mapped function with the greatest start below it is Thumb code, ends
  at or before the entry and has a closed control-flow graph, and the bytes from the end of its last
  reached instruction to the entry (a literal pool, dead code, padding, any unmapped gap), which its own
  paths never run but which would run on into the entry, are at most ``GAP_LIMIT`` and named by nothing
  (no word, BL, Thumb branch or ADR targets one of their halfwords); with no such function it refuses;
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
           "the function, or unmapped bytes before it, through an address formed at run time (by arithmetic, in "
           "decompressed data, or as a ROM mirror address assembled from bytes at an odd offset) rather than "
           "stored in the ROM, so its direct callers are all its callers")
MIRRORS = tuple(step * 0x01000000 for step in range(1, 6))     # 0x09000000-0x0DFFFFFF over 0x08000000
BRANCH_REACH = 4096
THUMB_ADR_REACH = 1028           # add rd, pc, #imm8 * 4 reaches ((pc + 4) & ~3) + 1020
GAP_LIMIT = 64                   # the most unreached bytes before the entry whose halfwords are scanned
_ARM_ADD, _ARM_SUB = 0b0010100, 0b0010010   # bits 27-21 of an ARM ADD/SUB immediate
_THUMB_BL = re.compile(rb"(?=[\x00-\xff][\xf0-\xf7][\x00-\xff][\xf8-\xff])", re.S)
_ARM_ADR = re.compile(rb"(?=[\x00-\xff][\x00-\xff][\x4f\x5f\x8f\x9f][\x02\x12\x22\x32\x42\x52\x62\x72\x82\x92"
                      rb"\xa2\xb2\xc2\xd2\xe2\xf2])", re.S)
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


def scan(rom, address, gap_start=None):
    """References in the ROM image to ``address`` or to a halfword of the unmapped gap [gap_start, address)
    before it: (words, BLs, Thumb B/B<cond>s, ADRs), each a sorted list of (site, target).

    Words are a target or its Thumb address at any byte offset, or either one in a ROM mirror at a
    halfword-aligned offset.  ADRs are the Thumb ``add rd, pc, #imm`` (it reaches 1020 bytes forward of its
    word-aligned PC) and ARM ADD/SUB immediates with Rn = PC at word-aligned offsets, any condition."""
    import match
    base = match.ROM_BASE
    first = address if gap_start is None else gap_start
    targets = set(range(first, address + 1, 2))
    words = []
    for target in sorted(targets):
        values = [(value, 1) for value in (target, target | 1)]
        values += [(value + mirror, 2) for mirror in MIRRORS for value in (target, target | 1)]
        for value, alignment in values:
            packed = struct.pack("<I", value)
            start = 0
            while (found := rom.find(packed, start)) >= 0:
                if found % alignment == 0:
                    words.append((base + found, target))
                start = found + 1
    calls = []
    for found in _THUMB_BL.finditer(rom):
        offset = found.start()
        if offset % 2:
            continue
        high, low = struct.unpack_from("<HH", rom, offset)
        displacement = ((high & 0x7FF) << 12) | ((low & 0x7FF) << 1)
        if displacement & 0x400000:
            displacement -= 0x800000
        if base + offset + 4 + displacement in targets:
            calls.append((base + offset, base + offset + 4 + displacement))
    branches = []
    for offset in range(max(0, (first - base - BRANCH_REACH) // 2 * 2),
                        min(len(rom) - 2, address - base + BRANCH_REACH) + 1, 2):
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
        if base + offset + 4 + displacement in targets:
            branches.append((base + offset, base + offset + 4 + displacement))
    adrs = []
    for offset in range(max(0, (first - base - THUMB_ADR_REACH) // 2 * 2), min(len(rom) - 2, address - base) + 1, 2):
        (half,) = struct.unpack_from("<H", rom, offset)
        target = ((base + offset + 4) & ~3) + (half & 0xFF) * 4
        if half & 0xF800 == 0xA000 and target in targets:
            adrs.append((base + offset, target))
    for found in _ARM_ADR.finditer(rom):
        offset = found.start()
        if offset % 4:
            continue
        (word,) = struct.unpack_from("<I", rom, offset)
        kind = (word >> 21) & 0x7F
        if kind not in (_ARM_ADD, _ARM_SUB) or (word >> 16) & 0xF != 15:
            continue
        rotate, immediate = (word >> 8) & 0xF, word & 0xFF
        value = (immediate >> 2 * rotate | immediate << 32 - 2 * rotate) & 0xFFFFFFFF if rotate else immediate
        target = (base + offset + 8 + (value if kind == _ARM_ADD else -value)) & 0xFFFFFFFE
        if target in targets:
            adrs.append((base + offset, target))
    return sorted(set(words)), sorted(calls), sorted(branches), sorted(set(adrs))


def _predecessor(proof, address):
    """(start, end, mode) of the mapped function, of any mode, with the greatest start below ``address``."""
    best = None
    for entry in proof.entries:
        start = int(entry["rom"], 16)
        if start < address and (best is None or start > best[0]):
            best = (start, int(entry["end"], 16), entry.get("mode", "thumb"))
    return best


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
        # Nothing falls into the entry: the mapped function before it never runs off its end, and nothing
        # names a byte after its last reached instruction (its tail, then any unmapped gap), from which
        # execution would run on into the entry.
        previous = _predecessor(proof, address)
        if previous is None:
            raise ValueError("no mapped function precedes it, so nothing shows that no code falls into its entry")
        if previous[2] != "thumb":
            raise ValueError(f"the function before it, 0x{previous[0]:08X}, is not Thumb code")
        if previous[1] > address:
            raise ValueError(f"the function before it, 0x{previous[0]:08X}, overlaps its entry")
        if address - previous[1] > GAP_LIMIT:
            raise ValueError(f"the {address - previous[1]} unreached bytes before its entry exceed {GAP_LIMIT}")
        try:
            refined = owner.refine(proof.span(previous[0]), previous[0], mapping)
        except ValueError:
            refined = dict(cfg_closed=False)
        if not refined["cfg_closed"]:
            raise ValueError(f"the function before it, 0x{previous[0]:08X}, may fall into its entry")
        reached = max((int(stop, 16) for _, stop in refined["code_ranges"]), default=previous[0])
        start = min(reached, previous[1])
        gap = address - start
        if gap > GAP_LIMIT:
            raise ValueError(f"the {gap} unreached bytes before its entry exceed {GAP_LIMIT}")
        words, sites, branches, adrs = scan(proof.rom, address, start if gap else None)

        def named(target):
            return "the function" if target == address else "the unreached bytes before it"
        if words:
            raise ValueError(f"the ROM word at 0x{words[0][0]:08X} names {named(words[0][1])}")
        outside = [(site, target) for site, target in branches if target != address or not own[0] <= site < own[1]]
        if outside:
            site, target = outside[0]
            raise ValueError(f"a Thumb branch at 0x{site:08X} reaches "
                             + ("the function's entry" if target == address else "the unreached bytes before it"))
        if adrs:
            raise ValueError(f"the ADR at 0x{adrs[0][0]:08X} forms the address of {named(adrs[0][1])}")
        into = [site for site, target in sites if target != address]
        if into:
            raise ValueError(f"a BL at 0x{into[0]:08X} branches into the unreached bytes before it")
        callers = []
        for site in [site for site, _ in sites]:
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
        found = dict(schema=SCHEMA, function=address, callers=callers, words=0, branches=0, adrs=0,
                     previous=previous[0], previous_end=previous[1], gap_start=start, gap=gap, premise=PREMISE,
                     premise_proved=False)
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
    gap = (f" and nothing names the {found['gap']} bytes from 0x{found['gap_start']:08X} to the entry, which "
           f"its control-flow graph never reaches" if found["gap"] else "")
    callers = ", ".join(f"0x{row['site']:08X} in 0x{row['caller']:08X} (R1 written at "
                        + " ".join(f"0x{node:08X}" for node in row["kills"]) + f"; {row['states']} states)"
                        for row in found["callers"])
    return [f"{LINE}: `{found['schema']}` own-frame addresses dropped at the owner's normal returns: {sites}; "
            f"no ROM word at any byte offset equals 0x{found['function']:08X} or 0x{found['function'] | 1:08X} "
            f"and no halfword-aligned one equals either in a ROM mirror (0x09000000-0x0DFFFFFF), "
            f"no Thumb branch outside it reaches its entry and no ADR forms its address; nothing falls into it: "
            f"the mapped function before it, 0x{found['previous']:08X}, has a closed control-flow graph{gap}; "
            f"every direct caller writes "
            f"R1 before any read, call or return: {callers}; {found['premise']}"]


def fingerprint_payload(proof):
    found = getattr(proof, "frame_result_r1", None)
    if not found:
        return None
    return json.dumps(["frame-result-r1-v1", found], sort_keys=True, separators=(",", ":")).encode()
