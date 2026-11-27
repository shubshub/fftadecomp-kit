"""The boot IWRAM code image: a call-via call into it is walked over the ROM bytes it was copied from.

FFTA runs three small Thumb routines (a clear, a fill and a copy) from IWRAM; the ROM table at
0x0836D4B8 holds their Thumb addresses, and callers reach them through `_call_via_rN`
(0x08005954 calls the clear at 0x08005984 while R3 still holds its caller's frame pointer).  The
buffer walks could not inspect such a call: the target is not in the cartridge's address space,
so the call refused.

The copy is derived from the ROM, at fixed addresses, every time; nothing about it is assumed:

* the cartridge entry word is `b` to the reset code, which runs straight to
  `ldr r1, =MAIN|1; mov lr, pc; bx r1`;
* MAIN runs straight to its call of BOOT, calling only call-free leaves before it;
* every path of BOOT from its entry reaches its call of the copier before any other call, return
  or PC write;
* the copier runs straight from its entry to `bl` CpuSet (the exact indexed wrapper
  `svc 0x0B; bx lr`), calling only that wrapper before it, with R0 (a ROM source), R1 (an IWRAM
  destination) and R2 (a copy control, not a fill) evaluated from its own literal words after its
  last earlier call (no value is carried across a call).

So when code in the image first runs, the image holds the copied ROM bytes (by the BIOS premise
every summarised CpuSet already states: CpuSet copies the units its control describes).  That it
still holds them when the call is made is NOT proved: IWRAM is writable by computed stores, DMA,
the image's own clear/fill/copy routines and later overlays.  The kit lists every aligned ROM word
whose value lies inside the image, which is all it can check.  Every report whose walk calls into
the image therefore records the premise `iwram-boot-image-unmodified-v1`, with that evidence and
the image's SHA-256, on one report line, all bound into its buffer fingerprint; a report without
such a call is unchanged.

The rule: call_via_target_profile (T2) resolves a `bl _call_via_rN` whose rN holds an exact value
C and asks `proof.call_via_resolvers` when C is not an indexed ROM entry.  This module's resolver
answers C & ~1 when C is odd and C & ~1 lies inside the derived image.  For an address it
answered, BufferCallProof.target and span (and the callee-saved walk's span) give the image bytes
from that address to the image's end at their IWRAM addresses, so the existing walks, summaries
and refusals apply to them unchanged.  Only the default path's two buffer proofs (exact types)
take the resolver; one line (POLICY) gates it.
"""
import array
import hashlib
import json
import struct

POLICY_NAME = 'iwram-boot-image-unmodified-v1'
FIELD = '* buffer IWRAM image'
PREMISE = ('the image is unmodified from the boot copy to each call: no computed store, DMA, '
           'image routine or later copy writes it (not proved; the listed ROM words are every '
           'aligned word whose value lies inside it)')
ROM_BASE = 0x08000000
IWRAM = (0x03000000, 0x03008000)
ENTRY_BRANCH = 0xEA00002E          # b 0x080000C0 at 0x08000000
RESET = 0x080000C0
MAIN = 0x08000254
MAIN_CALL = 0x08000276
BOOT = 0x08002710
BOOT_CALL = 0x08002742
COPIER = 0x08002768
COPY_SITE = 0x08002796
CPUSET = 0x0814186C


class Policy:
    """A maintainer's switch."""

    def __init__(self):
        self.enabled = True


POLICY = Policy()
_CACHE = {}


class Image:
    def __init__(self, destination, source, length, evidence):
        self.destination, self.source, self.length = destination, source, length
        self.evidence = evidence

    @property
    def end(self):
        return self.destination + self.length

    def contains(self, address):
        return self.destination <= address < self.end

    def bytes_from(self, rom, address):
        start = self.source + (address - self.destination) - ROM_BASE
        return bytes(rom[start:self.source + self.length - ROM_BASE])


def applies(proof):
    """The default path's two buffer proofs, of the match module that defined the proof (match.py
    issues as __main__ and replays as match: call_via_target_profile.kit_match)."""
    from call_via_target_profile import kit_match
    kit = kit_match(proof)
    return POLICY.enabled and type(proof) in (kit.BufferCallProof, kit.FunctionBufferCallProof)


# ---- the derivation --------------------------------------------------------------------------

def _thumb():
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    return decoder


def _word(rom, address):
    offset = address - ROM_BASE
    if not 0 <= offset <= len(rom) - 4 or address % 4:
        raise ValueError("IWRAM image evidence reads outside the ROM")
    return struct.unpack_from('<I', rom, offset)[0]


def _one(rom, decoder, address):
    """The Thumb instruction at `address`, decoded on its own (pool words never stop a decode)."""
    offset = address - ROM_BASE
    if not 0 <= offset <= len(rom) - 2:
        raise ValueError("IWRAM image boot path leaves the ROM")
    found = next(decoder.disasm(bytes(rom[offset:offset + 4]), address, 1), None)
    if found is None:
        raise ValueError(f"IWRAM image boot path has no instruction at 0x{address:08X}")
    return found


def _pc_literal(rom, instruction):
    """The word `ldr rd, [pc, #imm]` loads, or None for any other instruction."""
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_PC
    operands = instruction.operands
    if instruction.mnemonic != 'ldr' or len(operands) != 2 or operands[0].type != ARM_OP_REG or \
            operands[1].type != ARM_OP_MEM or operands[1].mem.base != ARM_REG_PC or operands[1].mem.index:
        return None
    return _word(rom, ((instruction.address + 4) & ~3) + operands[1].mem.disp)


def _control(instruction):
    from capstone import CS_GRP_CALL, CS_GRP_JUMP, CS_GRP_RET, CS_GRP_INT
    from capstone.arm import ARM_REG_PC
    if CS_GRP_CALL in instruction.groups:
        return 'call'
    if CS_GRP_JUMP in instruction.groups or CS_GRP_RET in instruction.groups or \
            CS_GRP_INT in instruction.groups or ARM_REG_PC in instruction.regs_access()[1]:
        return 'jump'
    return None


def _direct_call(instruction):
    return instruction.operands[0].imm if instruction.mnemonic == 'bl' and instruction.size == 4 else None


def _straight(rom, entry, site, *, what, calls):
    """The instructions from `entry` up to `site`: no branch, return or PC write, and each call a BL
    that `calls(target)` admits.  `site` must be an instruction boundary of that run."""
    decoder, run, current = _thumb(), [], entry
    while current < site:
        instruction = _one(rom, decoder, current)
        kind = _control(instruction)
        if kind == 'jump' or kind == 'call' and not calls(_direct_call(instruction)):
            raise ValueError(f"IWRAM image {what} does not run straight to its boot call")
        run.append(instruction)
        current += instruction.size
    if current != site:
        raise ValueError(f"IWRAM image {what} does not reach its boot call")
    return run


def _call_at(rom, site, target):
    instruction = _one(rom, _thumb(), site)
    if _direct_call(instruction) != target:
        raise ValueError(f"IWRAM image boot path has no call of 0x{target:08X} at 0x{site:08X}")


def _leaf(rom, address):
    """A call-free Thumb leaf: straight-line to `bx lr`, no other control transfer."""
    decoder, current = _thumb(), address
    for _ in range(128):
        instruction = _one(rom, decoder, current)
        if instruction.mnemonic == 'bx' and instruction.op_str == 'lr':
            return True
        if _control(instruction) is not None:
            return False
        current += instruction.size
    return False


def _dominated(rom, entry, site):
    """Every path from `entry` reaches `site` before any call, return or PC write."""
    from capstone.arm import ARM_CC_AL, ARM_CC_INVALID, ARM_INS_B
    decoder, pending, seen = _thumb(), [entry], set()
    while pending:
        current = pending.pop()
        if current == site or current in seen:
            continue
        if len(seen) > 256:
            raise ValueError("IWRAM image boot path is too long")
        seen.add(current)
        instruction = _one(rom, decoder, current)
        if instruction.id == ARM_INS_B:
            pending.append(instruction.operands[0].imm)
            if instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
                pending.append(current + instruction.size)
        elif _control(instruction) is not None:
            raise ValueError("IWRAM image boot path can call, return or jump before the copier")
        else:
            pending.append(current + instruction.size)


def _reset(rom):
    """The entry branch and the ARM reset code reach MAIN."""
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_ARM, CS_GRP_JUMP, CS_GRP_CALL
    from capstone.arm import ARM_REG_PC, ARM_CC_AL, ARM_CC_INVALID
    if _word(rom, ROM_BASE) != ENTRY_BRANCH:
        raise ValueError("IWRAM image cartridge entry does not branch to the reset code")
    decoder = Cs(CS_ARCH_ARM, CS_MODE_ARM)
    decoder.detail = True
    run = []
    for address in range(RESET, RESET + 0x40, 4):
        instruction = next(decoder.disasm(bytes(rom[address - ROM_BASE:address - ROM_BASE + 4]), address, 1), None)
        if instruction is None or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
            break
        if instruction.mnemonic == 'bx':
            if len(run) < 2 or instruction.op_str != 'r1':
                break
            load, link = run[-2], run[-1]
            if link.mnemonic != 'mov' or link.op_str != 'lr, pc' or load.mnemonic != 'ldr' or \
                    not load.op_str.startswith('r1, [pc, #') or load.operands[1].mem.index:
                break
            if _word(rom, load.address + 8 + load.operands[1].mem.disp) != MAIN | 1:
                break
            return
        if CS_GRP_JUMP in instruction.groups or CS_GRP_CALL in instruction.groups or \
                ARM_REG_PC in instruction.regs_access()[1]:
            break
        run.append(instruction)
    raise ValueError("IWRAM image reset code does not run straight to MAIN")


def _arguments(rom, run):
    """R0-R2 at the end of a straight run: PC-relative literals, immediate moves, register copies,
    register and immediate adds/subs and immediate shifts; a call forgets every value (nothing is
    carried across one, so no callee's preservation is assumed); anything else makes what it
    writes unknown."""
    from capstone import CS_GRP_CALL
    from capstone.arm import ARM_OP_IMM, ARM_OP_REG, ARM_REG_R0
    values = {}
    for instruction in run:
        operands = instruction.operands
        kinds = [operand.type for operand in operands]
        if CS_GRP_CALL in instruction.groups:
            values.clear()
            continue
        result = _pc_literal(rom, instruction)
        mnemonic = instruction.mnemonic
        if result is not None:
            pass
        elif mnemonic in ('movs', 'mov') and kinds == [ARM_OP_REG, ARM_OP_IMM]:
            result = operands[1].imm
        elif mnemonic in ('movs', 'mov') and kinds == [ARM_OP_REG, ARM_OP_REG]:
            result = values.get(operands[1].reg)
        elif mnemonic in ('adds', 'subs') and kinds == [ARM_OP_REG, ARM_OP_REG, ARM_OP_REG]:
            left, right = values.get(operands[1].reg), values.get(operands[2].reg)
            if left is not None and right is not None:
                result = (left + right if mnemonic == 'adds' else left - right) & 0xFFFFFFFF
        elif mnemonic in ('adds', 'subs') and kinds == [ARM_OP_REG, ARM_OP_REG, ARM_OP_IMM]:
            left = values.get(operands[1].reg)
            if left is not None:
                step = operands[2].imm
                result = (left + step if mnemonic == 'adds' else left - step) & 0xFFFFFFFF
        elif mnemonic in ('lsls', 'lsrs') and kinds == [ARM_OP_REG, ARM_OP_REG, ARM_OP_IMM] and \
                0 < operands[2].imm < 32:
            left = values.get(operands[1].reg)
            if left is not None:
                result = (left << operands[2].imm if mnemonic == 'lsls' else left >> operands[2].imm) & 0xFFFFFFFF
        for register in instruction.regs_access()[1]:
            values.pop(register, None)
        if result is not None:
            values[operands[0].reg] = result
    return [values.get(ARM_REG_R0 + number) for number in range(3)]


def _words_inside(rom, start, end):
    """[address, value] of every aligned ROM word whose value lies in [start, end)."""
    words = array.array('I')
    if words.itemsize != 4:
        raise ValueError("IWRAM image evidence needs 32-bit words")
    words.frombytes(bytes(rom[:len(rom) // 4 * 4]))
    return [[ROM_BASE + 4 * index, value] for index, value in enumerate(words) if start <= value < end]


def derive(rom, entries):
    """The boot IWRAM image, or ValueError saying which part of the boot copy is not proved.
    `entries` is the function index (the decoded config/functions.json)."""
    rows = [entry for entry in entries if isinstance(entry, dict) and isinstance(entry.get('rom'), str)
            and int(entry['rom'], 16) & ~1 == CPUSET]
    if len(rows) != 1 or rows[0].get('mode') != 'thumb' or int(rows[0]['rom'], 16) != CPUSET or \
            not isinstance(rows[0].get('end'), str) or int(rows[0]['end'], 16) != CPUSET + 4 or \
            len(rom) < CPUSET + 4 - ROM_BASE or \
            struct.unpack_from('<HH', rom, CPUSET - ROM_BASE) != (0xDF0B, 0x4770):
        raise ValueError("IWRAM image boot copy needs the exact indexed CpuSet wrapper")
    _reset(rom)
    _straight(rom, MAIN, MAIN_CALL, what='MAIN', calls=lambda target: target is not None and _leaf(rom, target))
    _call_at(rom, MAIN_CALL, BOOT)
    _dominated(rom, BOOT, BOOT_CALL)
    _call_at(rom, BOOT_CALL, COPIER)
    run = _straight(rom, COPIER, COPY_SITE, what='copier', calls=lambda target: target == CPUSET)
    _call_at(rom, COPY_SITE, CPUSET)
    source, destination, control = _arguments(rom, run)
    if source is None or destination is None or control is None:
        raise ValueError("IWRAM image copy arguments are not the copier's literal constants")
    if control & (1 << 24) or control & ~((1 << 26) | 0x1FFFFF):
        raise ValueError("IWRAM image boot CpuSet is not a plain copy")
    unit = 4 if control & (1 << 26) else 2
    length = (control & 0x1FFFFF) * unit
    if length == 0 or source % unit or destination % unit or \
            not ROM_BASE <= source <= source + length <= ROM_BASE + len(rom) or \
            not IWRAM[0] <= destination <= destination + length <= IWRAM[1]:
        raise ValueError("IWRAM image copy is not a ROM source and an IWRAM destination")
    evidence = dict(policy=POLICY_NAME, path=[RESET, MAIN, MAIN_CALL, BOOT, BOOT_CALL, COPIER, COPY_SITE, CPUSET],
                    source=source, destination=destination, length=length, unit=unit,
                    sha256=hashlib.sha256(bytes(rom[source - ROM_BASE:source + length - ROM_BASE])).hexdigest(),
                    words=_words_inside(rom, destination, destination + length))
    return Image(destination, source, length, evidence)


def image(proof):
    """The proof's derived image (memoised per ROM and mapping), or None when it is not proved."""
    if not hasattr(proof, 'iwram_image'):
        key = (hashlib.sha256(bytes(proof.rom)).digest(),
               hashlib.sha256(json.dumps(proof.entries, sort_keys=True).encode()).digest())
        if key not in _CACHE:
            try:
                _CACHE[key] = derive(proof.rom, proof.entries)
            except ValueError:
                _CACHE[key] = None
        proof.iwram_image = _CACHE[key]
    return proof.iwram_image


# ---- the rule --------------------------------------------------------------------------------

def resolver(proof, site, register, value):
    """call_via_resolvers entry: an exact odd value inside the derived image names its address."""
    if not applies(proof) or not isinstance(value, int) or not value & 1 or \
            not IWRAM[0] <= int(value) < IWRAM[1]:
        return None
    found = image(proof)
    address = int(value) & ~1
    if found is None or not found.contains(address):
        return None
    proof.iwram_image_calls.add((site, address))
    return address


def resolved(proof, address):
    """Whether `address` is an image address this proof's resolver answered."""
    return applies(proof) and getattr(proof, 'iwram_image', None) is not None and \
        any(target == address for _, target in proof.iwram_image_calls)


def target(proof, address):
    """BufferCallProof.target for an answered image address: a Thumb row to the image's end."""
    if not resolved(proof, address):
        return None
    return {"rom": f"0x{address:08X}", "end": f"0x{proof.iwram_image.end:08X}", "mode": "thumb"}


def span(proof, address):
    """BufferCallProof.span for an answered image address: the copied bytes from there to the end."""
    if not resolved(proof, address):
        return None
    return proof.iwram_image.bytes_from(proof.rom, address)


def watch_target(proof):
    """The callee-saved walks' resolver hook (callee_saved_watch.Checker.resolve): an exact odd value
    inside the derived image, as a call-via destination at `site`, is that routine's address.  The
    call is noted on the proof (never rolled back, as those walks' premises are not) and stated with
    the buffer walks' own (`record`)."""
    def lookup(value, site):
        if not applies(proof) or not isinstance(value, int) or not value & 1 or \
                not IWRAM[0] <= int(value) < IWRAM[1]:
            return None
        found = image(proof)
        address = int(value) & ~1
        if found is None or not found.contains(address):
            return None
        proof.iwram_image_watch_calls.add((site, address))
        return address
    return lookup


def watch_span(proof):
    """The callee-saved walks' span hook: (bytes, end) for an image address any walk answered."""
    def lookup(address):
        if not resolved(proof, address) and not any(target == address for _, target in proof.iwram_image_watch_calls):
            return None
        found = image(proof)
        return found.bytes_from(proof.rom, address), found.end
    return lookup


def calls(proof):
    """Every (site, address) call into the image: the buffer walks' and the callee-saved walks'."""
    return set(getattr(proof, 'iwram_image_calls', ())) | set(getattr(proof, 'iwram_image_watch_calls', ()))


def record(proof):
    if not applies(proof):
        return None
    found = calls(proof)
    if not found:
        return None
    return dict(image(proof).evidence, premise=PREMISE, calls=[list(call) for call in sorted(found)])


def fingerprint_payload(proof):
    evidence = record(proof)
    return None if evidence is None else json.dumps(evidence, sort_keys=True, separators=(',', ':')).encode()


def lines(proof):
    evidence = record(proof)
    if evidence is None:
        return []
    start, length = evidence['destination'], evidence['length']
    calls = ', '.join(f"0x{site:08X} -> 0x{address:08X}" for site, address in evidence['calls'])
    words = ', '.join(f"0x{site:08X}=0x{value:08X}" for site, value in evidence['words']) or 'none'
    return [f"{FIELD}: `{POLICY_NAME}` 0x{start:08X}-0x{start + length:08X} = ROM 0x{evidence['source']:08X} "
            f"({length} bytes, SHA-256 {evidence['sha256']}) copied by CpuSet at 0x{COPY_SITE:08X} in "
            f"0x{COPIER:08X}, reached on every path 0x{RESET:08X} -> 0x{MAIN:08X} -> 0x{BOOT:08X} -> "
            f"0x{COPIER:08X}; calls {calls}; ROM words inside {words}; premise: {PREMISE}"]
