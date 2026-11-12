"""Explicit conditional BIOS CpuSet fill source within a live local frame.

Only the source read is bounded here. The BIOS operation and ordinary return
are explicit premises, not consequences of the SWI wrapper's four bytes.
"""
import hashlib
import json
from capstone import CS_GRP_CALL
from capstone.arm_const import (ARM_CC_AL, ARM_CC_INVALID, ARM_OP_IMM,
    ARM_OP_MEM, ARM_OP_REG, ARM_REG_PC, ARM_REG_R0)

ADDRESS = 0x0814186C
NAME = 'func_0814186C'
WRAPPER = bytes.fromhex('0bdf7047')
SCHEMA = 'conditional-bios-cpuset-local-fill-source-v1'
CONTRACT = ('conditional returning GBA BIOS CpuSet fill boundary: bit24 selects '
            'one source unit, bit26 selects 16/32-bit width; local source span '
            'only, external destination is caller supplied; known bits in '
            'r4-r11 survive calls under the conditional ordinary returning ABI; '
            'no initialization, '
            'physical readability, physical nonalias, destination bounds, '
            'numeric result or termination theorem')
MASK = 0xFFFFFFFF
MAX_UPDATES = 4096
LOCAL_SOURCE_CONTRACT = (
    'bounded local fill source address is used only to read one initialized '
    'unit; no numeric source-pointer observation or retention; exact source '
    'content, destination and control; opaque outputs retain raw arguments; '
    'no physical readability, physical nonalias, destination extent or '
    'termination theorem')


class ConditionalVolatileInterfaces:
    """Read sets under the explicitly selected, freshly checked fill premise.

    The SWI bytes do not prove the BIOS register interface. No guaranteed
    overwrite is asserted, so a later read of r3 still keeps its value live.
    Complete original-ELF admission remains the selected profile's job.
    The default/legacy selector authorizes only that register interface.
    BIOS_LOCAL_FILL_SELECTOR separately opts in to LOCAL_SOURCE_CONTRACT and
    authenticates its distinct native manifest before exposing that premise.
    """

    def __init__(self, ordinary, data, address, rom, mapping, index, objects, *,
                 selector=None):
        import owner_admission_profile as owner
        import named_data_buffer_profile as named
        selector = named.BIOS_FILL_SELECTOR if selector is None else selector
        if selector not in (named.BIOS_FILL_SELECTOR, named.BIOS_LOCAL_FILL_SELECTOR):
            raise ValueError('unknown conditional CpuSet semantic policy selector')
        manifest, _, _ = owner.preflight(data, address, rom, mapping, index,
                                         objects, selector=selector)
        fingerprint = hashlib.sha256(json.dumps(manifest, sort_keys=True,
            separators=(',', ':')).encode()).hexdigest()
        self.ordinary = ordinary
        self.local_fill_premise = (LOCAL_SOURCE_CONTRACT +
            '; native fill preflight SHA-256 ' + fingerprint
            if selector == named.BIOS_LOCAL_FILL_SELECTOR else None)
        self.conditional_premises = {NAME:
            'conditional returning CpuSet consumes only r0-r2; no guaranteed '
            'register overwrite; native fill preflight SHA-256 ' + fingerprint}

    def __call__(self, name):
        if name == NAME:
            return {'r0', 'r1', 'r2'}, set()
        return self.ordinary(name) if self.ordinary is not None else None


def scalar_control_words(instructions, edges, calls, partition, address):
    """Recognize literal words used solely as the actual CpuSet R2 control."""
    result = []
    register = ARM_REG_R0 + 2
    for word in partition['words']:
        if not word['load_sites'] or word['switch_word'] or not word['value'] & (1 << 24):
            continue
        sites = []
        for load in word['load_sites']:
            item = instructions[load]
            op = item.operands
            code = int.from_bytes(item.bytes, 'little')
            if item.size != 2 or code & 0xFF00 != 0x4A00 or \
                    item.mnemonic != 'ldr' or len(op) != 2 or \
                    op[0].type != ARM_OP_REG or op[0].reg != register or \
                    op[1].type != ARM_OP_MEM or op[1].mem.base != ARM_REG_PC or \
                    op[1].mem.index or item.writeback or \
                    ((load + 4) & ~3) + op[1].mem.disp != word['address']:
                break
            cursor, visited, use = load, {load}, None
            while len(edges[cursor]) == 1:
                successor = edges[cursor][0]
                if successor in visited or successor != cursor + instructions[cursor].size:
                    break
                visited.add(successor)
                following = instructions[successor]
                if successor in calls:
                    if calls[successor] == ADDRESS:
                        use = successor
                    break
                reads, writes = following.regs_access()
                if register in reads or register in writes:
                    break
                cursor = successor
            if use is None:
                break
            sites.append([load-address, use-address])
        if len(sites) == len(word['load_sites']):
            result.append([word['address']-address, word['value'], sites])
    return result


def saved_scalar_control_words(instructions, edges, calls, partition, address):
    """Closed linear scalar-only copies from a low callee-saved literal load."""
    result = []
    low_saved = set(range(ARM_REG_R0 + 4, ARM_REG_R0 + 8))
    arguments = set(range(ARM_REG_R0, ARM_REG_R0 + 4))
    control = ARM_REG_R0 + 2
    for word in partition['words']:
        if not word['load_sites'] or word['switch_word'] or not word['value'] & (1 << 24):
            continue
        observations = []
        for load in word['load_sites']:
            item = instructions[load]
            op = item.operands
            code = int.from_bytes(item.bytes, 'little')
            if item.size != 2 or code & 0xFC00 != 0x4C00 or item.mnemonic != 'ldr' or \
                    len(op) != 2 or op[0].type != ARM_OP_REG or \
                    op[0].reg != ARM_REG_R0 + ((code >> 8) & 7) or \
                    op[0].reg not in low_saved or op[1].type != ARM_OP_MEM or \
                    op[1].mem.base != ARM_REG_PC or op[1].mem.index or item.writeback or \
                    ((load + 4) & ~3) + op[1].mem.disp != word['address']:
                break
            aliases, cursor, visited, uses = {op[0].reg}, load, {load}, []
            valid = True
            while aliases:
                successor = cursor + instructions[cursor].size
                if edges[cursor] != (successor,) or successor in visited:
                    valid = False
                    break
                visited.add(successor)
                following = instructions[successor]
                if successor in calls:
                    if aliases & (arguments - {control}) or \
                            control in aliases and calls[successor] != ADDRESS:
                        valid = False
                        break
                    if control in aliases:
                        uses.append(successor - address)
                    # Exactly the existing conditional ordinary returning ABI.
                    aliases -= arguments
                else:
                    reads, writes = map(set, following.regs_access())
                    copied = None
                    if aliases & reads:
                        code = int.from_bytes(following.bytes, 'little')
                        if following.size == 2 and (code & 0xFF00 == 0x4600 or
                                                    code & 0xFFC0 == 0x1C00):
                            copied = transfer(following,
                                {reg: exact(word['value']) for reg in aliases}, b'', 0)
                        if copied is None or copied[0] not in low_saved | {control} or \
                                copied[1] != exact(word['value']):
                            valid = False
                            break
                    aliases -= writes
                    if copied is not None:
                        aliases.add(copied[0])
                cursor = successor
            if not valid or not uses:
                break
            observations.append([load - address, uses])
        if len(observations) == len(word['load_sites']):
            result.append([word['address'] - address, word['value'], observations])
    return result


def exact(value):
    value &= MASK
    return value, MASK ^ value


def transfer(instruction, incoming, data, address):
    """Introduce bits only from authenticated native Thumb encodings."""
    if instruction.size != 2 or instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID):
        return None
    op = instruction.operands
    code = int.from_bytes(instruction.bytes, 'little')
    name = instruction.mnemonic
    if code & 0xF800 == 0x2000 and name == 'movs' and len(op) == 2 and \
            op[0].type == ARM_OP_REG and op[1].type == ARM_OP_IMM and \
            op[0].reg == ARM_REG_R0 + ((code >> 8) & 7) and op[1].imm == (code & 255):
        return op[0].reg, exact(op[1].imm)
    if code & 0xFF00 == 0x4600 and name == 'mov' and len(op) == 2 and \
            all(p.type == ARM_OP_REG for p in op):
        destination = ARM_REG_R0 + (code & 7) + ((code >> 4) & 8)
        source = ARM_REG_R0 + ((code >> 3) & 15)
        if (op[0].reg, op[1].reg) == (destination, source):
            return destination, incoming.get(source, (0, 0))
    if code & 0xFFC0 == 0x1C00 and name == 'adds' and len(op) == 3 and \
            op[0].type == op[1].type == ARM_OP_REG and op[2].type == ARM_OP_IMM and op[2].imm == 0:
        destination, source = ARM_REG_R0 + (code & 7), ARM_REG_R0 + ((code >> 3) & 7)
        if (op[0].reg, op[1].reg) == (destination, source):
            return destination, incoming.get(source, (0, 0))
    kind = code & 0xF800
    if kind in (0x0000, 0x0800) and name in ('lsls', 'lsrs') and len(op) == 3 and \
            op[0].type == op[1].type == ARM_OP_REG and op[2].type == ARM_OP_IMM:
        destination, source = ARM_REG_R0 + (code & 7), ARM_REG_R0 + ((code >> 3) & 7)
        shift = (code >> 6) & 31
        if kind == 0x0800 and shift == 0:
            shift = 32
        if (op[0].reg, op[1].reg, op[2].imm) == (destination, source, shift) and \
                name == ('lsls' if kind == 0 else 'lsrs'):
            ones, zeros = incoming.get(source, (0, 0))
            bits = (((ones << shift) & MASK, ((zeros << shift) | ((1 << shift)-1)) & MASK)
                    if kind == 0 else (ones >> shift, (zeros >> shift) | (MASK ^ (MASK >> shift))))
            return destination, bits
    kind = code & 0xFFC0
    if kind in (0x4000, 0x4300, 0x4380) and name == {0x4000:'ands', 0x4300:'orrs', 0x4380:'bics'}[kind] and \
            len(op) == 2 and all(p.type == ARM_OP_REG for p in op):
        destination, source = ARM_REG_R0 + (code & 7), ARM_REG_R0 + ((code >> 3) & 7)
        if (op[0].reg, op[1].reg) == (destination, source):
            ao, az = incoming.get(destination, (0, 0))
            bo, bz = incoming.get(source, (0, 0))
            bits = ((ao & bo, az | bz) if kind == 0x4000 else
                    (ao | bo, az & bz) if kind == 0x4300 else (ao & bz, az | bo))
            return destination, bits
    if code & 0xF800 == 0x4800 and name == 'ldr' and len(op) == 2 and \
            op[0].type == ARM_OP_REG and op[1].type == ARM_OP_MEM and \
            op[0].reg == ARM_REG_R0 + ((code >> 8) & 7) and \
            op[1].mem.base == ARM_REG_PC and not op[1].mem.index and \
            op[1].mem.disp == (code & 255)*4 and not instruction.writeback:
        offset = ((instruction.address + 4) & ~3) + op[1].mem.disp - address
        if not 0 <= offset <= len(data)-4:
            raise ValueError('BIOS fill control literal escapes the complete owner')
        return op[0].reg, exact(int.from_bytes(data[offset:offset+4], 'little'))
    return None


def prove_bits(instructions, edges, address, data):
    """Intersect joins, retaining only ABI callee-saved facts across calls."""
    if address not in instructions or set(edges) != set(instructions):
        raise ValueError('BIOS fill bits require an exact closed native CFG')
    states, pending, updates = {address:{}}, [address], 0
    while pending:
        site = pending.pop()
        instruction, incoming = instructions[site], states[site]
        outgoing = dict(incoming)
        if CS_GRP_CALL in instruction.groups:
            outgoing = {register:bits for register,bits in incoming.items()
                        if ARM_REG_R0 + 4 <= register <= ARM_REG_R0 + 11}
        else:
            for register in instruction.regs_access()[1]:
                outgoing.pop(register, None)
            result = transfer(instruction, incoming, data, address)
            if result is not None and result[1] != (0, 0):
                outgoing[result[0]] = result[1]
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError('BIOS fill CFG escapes an instruction boundary')
            previous = states.get(successor)
            merged = dict(outgoing) if previous is None else {
                register:(ones & outgoing[register][0], zeros & outgoing[register][1])
                for register,(ones,zeros) in previous.items() if register in outgoing}
            merged = {register:bits for register,bits in merged.items() if bits != (0,0)}
            if merged != previous:
                updates += 1
                if updates > MAX_UPDATES:
                    raise ValueError('BIOS fill bit proof-state budget exhausted')
                states[successor] = merged
                pending.append(successor)
    if set(states) != set(instructions):
        raise ValueError('BIOS fill facts omit reached native instructions')
    return states


class BiosFillProof:
    def __init__(self, data, address, rom, mapping, index, calls):
        import match
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        owner.validate_span(data, address, rom, mapping, index)
        refinement = owner.refine(data, address, mapping)
        instructions, edges, branches, actual, words = graph.graph(data, address, refinement)
        if branches or words or calls != actual or ADDRESS not in calls.values():
            raise ValueError('BIOS fill requires an actual direct call in its closed owner')
        graph.partition(data, address, refinement, instructions, words)
        offset = ADDRESS - match.ROM_BASE
        body = rom[offset:offset+len(WRAPPER)]
        if body != WRAPPER:
            raise ValueError('BIOS fill requires the exact CpuSet SWI 0x0B return wrapper')
        owner.validate_span(body, ADDRESS, rom, mapping, index)
        self.data, self.address = data, address
        self.rom, self.mapping, self.index = rom, mapping, index
        self.calls = dict(calls)
        self.wrapper = body
        self.states = prove_bits(instructions, edges, address, data)
        self.observations = set()

    def check_call(self, site, aliases, stack):
        import match
        if type(site) is not int or self.calls.get(site) != ADDRESS or \
                set(aliases) != {ARM_REG_R0}:
            raise ValueError('BIOS fill requires only a local R0 source and an external destination')
        ones, zeros = self.states[site].get(ARM_REG_R0 + 2, (0, 0))
        if not ones & (1 << 24):
            raise ValueError('BIOS fill mode bit24 is not set on every reaching path')
        # Unknown width is conservatively a complete aligned 32-bit source unit.
        width = 2 if zeros & (1 << 26) else 4
        offset = aliases[ARM_REG_R0]
        match.BufferCallProof.access(offset, width, stack)
        self.observations.add((site, offset, width, ones, zeros))
        return {}

    def manifest(self):
        return dict(schema=SCHEMA, contract=CONTRACT,
                    owner=[self.address, len(self.data), hashlib.sha256(self.data).hexdigest()],
                    dependency=[ADDRESS, len(self.wrapper), hashlib.sha256(self.wrapper).hexdigest()],
                    sites=[list(row) for row in sorted(self.observations)])

    def fingerprint(self):
        return hashlib.sha256(json.dumps(self.manifest(), sort_keys=True,
                                         separators=(',', ':')).encode()).hexdigest()
