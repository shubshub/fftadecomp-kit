"""Authenticate a ROM-backed CpuSet code-image plan, not installed RAM effects.

An exact call-site argument relation does not prove that the call executes, that
BIOS implements the copy, or that the copied bytes persist until a later fetch.
This opt-in prerequisite deliberately leaves those obligations open. No address
from a data map is used as allocation, readability or installed-code authority.
"""
import hashlib

from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB, CS_GRP_CALL
from capstone.arm import ARM_OP_REG, ARM_REG_R0, ARM_REG_PC

import bios_cpuset_fill_profile as bios
import owner_graph_profile as graph
import owner_runtime_profile as operations
import software_double_profile as indexed

SELECTOR = 'rom-cpuset-code-image-provenance-v1'
SCHEMA = 'rom-cpuset-code-image-prerequisite-v1'
ROM_BASE = 0x08000000
MAX_OWNER = 4096
MAX_IMAGE = 1024
MAX_UPDATES = 8192
MASK = 0xffffffff


def _constant_transfer(item, incoming, data, address):
    bits = {reg: bios.exact(value) for reg, value in incoming.items()}
    result = bios.transfer(item, bits, data, address)
    if result is not None and result[1][0] | result[1][1] == MASK:
        return result[0], result[1][0]
    # Thumb-1 SUBS Rd, Rn, Rm. Check both encoding and decoder operands.
    raw = int.from_bytes(item.bytes, 'little')
    if item.size == 2 and raw & 0xfe00 == 0x1a00 and item.mnemonic == 'subs':
        regs = (ARM_REG_R0 + (raw & 7), ARM_REG_R0 + ((raw >> 3) & 7),
                ARM_REG_R0 + ((raw >> 6) & 7))
        if len(item.operands) == 3 and all(op.type == ARM_OP_REG for op in item.operands) \
                and tuple(op.reg for op in item.operands) == regs \
                and all(reg in incoming for reg in regs[1:]):
            return regs[0], (incoming[regs[1]] - incoming[regs[2]]) & MASK
    return None


def constant_states(instructions, edges, address, data):
    """Exact all-path constants, intersecting joins and killing ALL on calls."""
    if set(edges) != set(instructions) or address not in instructions or \
            any(target not in instructions for values in edges.values() for target in values):
        raise ValueError('installation constants require the exact closed owner CFG')
    states, pending, updates = {address: {}}, [address], 0
    while pending:
        site = pending.pop()
        item, incoming = instructions[site], states[site]
        outgoing = {}
        if CS_GRP_CALL not in item.groups and item.mnemonic != 'svc':
            outgoing = {reg: value for reg, value in incoming.items()
                        if reg not in item.regs_access()[1]}
            result = _constant_transfer(item, incoming, data, address)
            if result is not None:
                outgoing[result[0]] = result[1]
        for target in edges[site]:
            previous = states.get(target)
            joined = dict(outgoing) if previous is None else {
                reg: value for reg, value in previous.items() if outgoing.get(reg) == value}
            if previous != joined:
                states[target] = joined
                pending.append(target)
                updates += 1
                if updates > MAX_UPDATES:
                    raise ValueError('installation constant-state bound exhausted')
    if set(states) != set(instructions):
        raise ValueError('installation constants omit reached instructions')
    return states


def image_inventory(payload, destination, entry):
    """Decode the source image at its proposed destination, stopping at BX.

This is a byte/edge inventory only. In particular, a POP/BX is recorded as an
unproved indirect endpoint, never inferred to return through an intact save.
Unreached image bytes remain explicit; no synthetic function-map row is made.
"""
    if type(payload) is not bytes or not 2 <= len(payload) <= MAX_IMAGE or \
            type(destination) is not int or type(entry) is not int or \
            destination % 2 or entry % 2 or not 0 <= destination < destination + len(payload) <= 1 << 32 \
            or not destination <= entry < destination + len(payload):
        raise ValueError('image inventory requires a bounded aligned entry within exact bytes')
    end = destination + len(payload)
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    pending, ins, edges, indirect, covered = [entry], {}, {}, [], set()
    allowed = {'push', 'pop', 'adds', 'subs', 'movs', 'mov', 'cmp', 'ands',
               'ldm', 'stm', 'ldrb', 'strb', 'ldr', 'str', 'lsls', 'lsrs'}
    while pending:
        site = pending.pop()
        if site in ins:
            continue
        if site % 2 or not destination <= site < end:
            raise ValueError('image control edge leaves exact copied bytes')
        item = next(decoder.disasm(payload[site-destination:site-destination+4], site, 1), None)
        if item is None or item.size != 2 or site + 2 > end:
            raise ValueError('image inventory excludes undecoded or non-Thumb-1 instructions')
        raw = int.from_bytes(item.bytes, 'little')
        successors = [site + 2]
        if raw & 0xff87 == 0x4700 and item.mnemonic == 'bx':
            successors = []
            indirect.append(dict(site=site, register=item.reg_name(item.operands[0].reg),
                                 resolved_return=False))
        elif raw & 0xf800 == 0xe000 and item.mnemonic == 'b':
            displacement = (raw & 0x7ff) << 1
            if displacement & 0x800:
                displacement -= 0x1000
            successors = [site + 4 + displacement]
        elif raw & 0xf000 == 0xd000 and (raw >> 8) & 15 < 14 and item.mnemonic.startswith('b'):
            displacement = (raw & 255) << 1
            if displacement & 0x100:
                displacement -= 0x200
            successors.append(site + 4 + displacement)
        elif item.mnemonic not in allowed or ARM_REG_PC in item.regs_access()[0] \
                or ARM_REG_PC in item.regs_access()[1] or CS_GRP_CALL in item.groups:
            raise ValueError('image inventory encountered an unsupported control or PC-dependent instruction')
        occupied = {site, site+1}
        if occupied & covered:
            raise ValueError('image instruction boundaries overlap')
        covered.update(occupied)
        ins[site] = dict(site=site, bytes=item.bytes.hex(), mnemonic=item.mnemonic,
                         operands=item.op_str, source_offset=site-destination)
        edges[site] = successors
        pending.extend(successors)
    if any(target not in ins for values in edges.values() for target in values):
        raise ValueError('image branch target is not an exact decoded boundary')
    return dict(instructions=[ins[site] for site in sorted(ins)],
                edges=[dict(site=site, targets=edges[site]) for site in sorted(edges)],
                indirect_endpoints=sorted(indirect, key=lambda row: row['site']),
                reached_bytes=len(covered), unvisited_offsets=[at for at in range(len(payload))
                    if destination+at not in covered], semantic_effects_proved=False,
                installed_memory_identity_proved=False)


def verify(data, address, rom, mapping, index, *, selector, call_site, pointer_address):
    """Bind complete indexed installer, actual SWI wrapper and ROM pointer."""
    if selector != SELECTOR or type(selector) is not str:
        raise ValueError('installation image requires its explicit prerequisite selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or \
            type(address) is not int or type(call_site) is not int or type(pointer_address) is not int \
            or not 2 <= len(data) <= MAX_OWNER:
        raise ValueError('installation image requires bounded immutable complete inputs')
    # Scheduler providers also use this installer while the owner profiles load.
    import owner_admission_profile as owner

    owner.validate_span(data, address, rom, mapping, index)
    refined = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refined)
    if branches or words:
        raise ValueError('installation image excludes local BL and table dispatch')
    partition = graph.partition(data, address, refined, instructions, words)
    operations.verify_operations(instructions, edges, address, branches, calls, refined)
    entries, rows = indexed.indices(mapping, index)
    record = indexed.span_record(address, address+len(data), entries, rows, rom)
    if record['instrs'] != len(instructions):
        raise ValueError('installation instruction count differs from both indices')
    if calls.get(call_site) != bios.ADDRESS:
        raise ValueError('installation site is not an actual direct CpuSet wrapper call')
    offset = bios.ADDRESS - ROM_BASE
    wrapper = rom[offset:offset+len(bios.WRAPPER)]
    wrapper_row = indexed.span_record(bios.ADDRESS, bios.ADDRESS+len(bios.WRAPPER), entries, rows, rom)
    if wrapper != bios.WRAPPER or wrapper_row['instrs'] != 2:
        raise ValueError('installation requires complete exact indexed SWI0B/BX wrapper')
    states = constant_states(instructions, edges, address, data)
    arguments = states[call_site]
    if any(ARM_REG_R0 + n not in arguments for n in range(3)):
        raise ValueError('installation arguments are not exact on every reaching path')
    source, destination, control = (arguments[ARM_REG_R0+n] for n in range(3))
    # Deliberately only the bounded positive copy subset. No fill/reserved bits.
    count = control & 0x1fffff
    width = 4 if control & 0x04000000 else 2
    if control & ~(0x04000000 | 0x1fffff) or not 1 <= count <= MAX_IMAGE // width:
        raise ValueError('installation control is not a bounded positive CpuSet copy')
    size = count * width
    if source % width or destination % width or \
            not ROM_BASE <= source < source+size <= ROM_BASE+len(rom) or \
            not 0x03000000 <= destination < destination+size <= 0x03008000:
        raise ValueError('installation numeric copy spans are unaligned or outside ROM/IWRAM aperture')
    if pointer_address % 4 or not ROM_BASE <= pointer_address <= ROM_BASE+len(rom)-4:
        raise ValueError('installation entry pointer must be a complete aligned ROM word')
    pointer = int.from_bytes(rom[pointer_address-ROM_BASE:pointer_address-ROM_BASE+4], 'little')
    entry = pointer & ~1
    if not pointer & 1 or not destination <= entry < destination+size:
        raise ValueError('installation Thumb entry is not within this exact copied image')
    payload = rom[source-ROM_BASE:source-ROM_BASE+size]
    inventory = image_inventory(payload, destination, entry)
    return dict(schema=SCHEMA, selector=selector,
        installer=dict(address=address, bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
                       instructions=len(instructions), partition=partition),
        wrapper=dict(address=bios.ADDRESS, bytes=wrapper.hex()), call_site=call_site,
        arguments=dict(source=source, destination=destination, control=control),
        copy_plan=dict(units=count, width=width, bytes=size, source=[source, source+size],
                       destination=[destination, destination+size]),
        source_image=dict(bytes=payload.hex(), sha256=hashlib.sha256(payload).hexdigest()),
        entry=dict(pointer_address=pointer_address, pointer_word=pointer, address=entry,
                   image_offset=entry-destination, source_address=source+entry-destination),
        inventory=inventory,
        input_sha256=dict(rom=hashlib.sha256(rom).hexdigest(), mapping=hashlib.sha256(mapping).hexdigest(),
                          index=hashlib.sha256(index).hexdigest()),
        all_call_register_facts_killed=True,
        installed_identity_proved=False, native_admission=False,
        obligations=['Actual execution and reachability of installation before callback',
            'Actual BIOS copy effects, normal return, accessible source and writable destination',
            'Memory and protected-frame safety of every earlier installer/startup action',
            'Persistence/no-overwrite of image through all intervening actions and code fetch',
            'Indirect endpoint, complete callback memory/frame/effects and caller composition'],
        limits='Exact static ROM-image/call-argument relation only. IWRAM numerical aperture '
               'does not grant allocation, readability, writability, physical separation or '
               'persistence. CFG continuation after earlier calls is conditional on their '
               'ordinary return; no register survival or effects premise is introduced.')
