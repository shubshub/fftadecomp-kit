"""One unsigned-guarded Thumb table with five reached interposed literal words.

This is ROM/CFG composition only. It grants no ELF relocation, source or call ABI
permission; the enclosing canonical-thunk profile retains those separate gates.
"""
import hashlib
import struct

SCHEMA = 'canonical-thunk-five-word-pool-switch-v1'


def discover(data, address, instructions):
    """Return one exact candidate, never infer an arbitrary indirect successor."""
    from match import ARM_OP_MEM, ARM_OP_REG, ARM_REG_PC, switch_layout
    result = []
    by_address = {item.address: item for item in instructions}
    for item in instructions:
        if item.mnemonic != 'mov' or len(item.operands) != 2 or \
                item.operands[0].type != ARM_OP_REG or item.operands[0].reg != ARM_REG_PC:
            continue
        load = by_address.get(item.address - 6)
        compare = by_address.get(item.address - 14)
        if load is None or compare is None or load.mnemonic != 'ldr' or \
                len(load.operands) != 2 or load.operands[1].type != ARM_OP_MEM or \
                load.operands[1].mem.base != ARM_REG_PC or load.operands[1].mem.index:
            continue
        from match import ARM_OP_IMM
        if compare.mnemonic != 'cmp' or len(compare.operands) != 2 or \
                compare.operands[1].type != ARM_OP_IMM or not 0 <= compare.operands[1].imm <= 255:
            continue
        literal = (((load.address + 4) & ~3) + load.operands[1].mem.disp) - address
        end = literal + 4 + 4 * (compare.operands[1].imm + 1)
        if literal < 20 or (address + literal) % 4 or end > len(data):
            continue
        relocations = {offset: struct.unpack_from('<I', data, offset)[0] - address
                       for offset in range(literal, end, 4)}
        try:
            descriptor = layout(data, address, relocations)
        except ValueError:
            continue
        if descriptor['dispatch'] + 8 == item.address - address:
            result.append(relocations)
    if len(result) != 1:
        raise ValueError('five-word pool requires one exact guarded switch')
    return result[0]


def layout(data, address, relocations):
    from match import switch_layout
    # The real encoding uses CMP; BLS dispatch; B default. Other guard
    # encodings remain outside this optional composition.
    descriptor = switch_layout(data, address, relocations, interposed_words=5)
    if descriptor['dispatch'] - descriptor['comparison'] != 6:
        raise ValueError('five-word pool requires adjacent unsigned low guard and default branch')
    return descriptor


def record(data, address, relocations, instructions):
    from match import ARM_OP_MEM, ARM_REG_PC
    descriptor = layout(data, address, relocations)
    starts = {item.address - address for item in instructions}
    code = set()
    loads = {}
    for item in instructions:
        code.update(range(item.address - address, item.address - address + item.size))
        for operand in item.operands:
            if item.mnemonic == 'ldr' and operand.type == ARM_OP_MEM and \
                    operand.mem.base == ARM_REG_PC and not operand.mem.index:
                offset = ((item.address + 4) & ~3) + operand.mem.disp - address
                if offset < 0 or (address + offset) % 4 or offset + 4 > len(data):
                    raise ValueError('five-word pool requires complete local literal words')
                loads.setdefault(offset, []).append(item.address - address)
    pool = range(descriptor['literal'] - 20, descriptor['literal'], 4)
    if any(offset not in loads for offset in pool):
        raise ValueError('every interposed pool word requires a reached PC-relative load')
    if any(addend not in starts for offset, addend in relocations.items()
           if offset != descriptor['literal']) or descriptor['default'] not in starts:
        raise ValueError('pool-switch cases and default must be reached instruction starts')
    words = set(relocations) | set(loads)
    literal_bytes = {position for offset in words for position in range(offset, offset + 4)}
    if code & literal_bytes:
        raise ValueError('pool-switch literal words overlap reached code')
    missing = set(range(len(data))) - code - literal_bytes
    # Only a zero halfword immediately preceding an aligned reached literal
    # may be alignment. No arbitrary zero padding is accepted.
    for offset in sorted(missing):
        if offset & 1:
            continue
        if offset + 1 not in missing or (address + offset) % 4 != 2 or \
                offset + 2 not in words or data[offset:offset + 2] != b'\0\0':
            raise ValueError('pool switch has unclassified complete-body bytes')
    if any(offset & 1 and offset - 1 not in missing for offset in missing):
        raise ValueError('pool switch has unclassified odd byte')
    return {'schema': SCHEMA, 'layout': descriptor,
            'body_sha256': hashlib.sha256(data).hexdigest(),
            'table_sha256': hashlib.sha256(data[descriptor['literal']:
                               descriptor['table'] + 4 * (descriptor['bound'] + 1)]).hexdigest(),
            'pool': [[offset, struct.unpack_from('<I', data, offset)[0], sorted(set(loads[offset]))]
                     for offset in pool]}
