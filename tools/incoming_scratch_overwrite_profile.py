"""Explicit incoming-scratch kill before an ordinary conditional-ABI call.

This proves only that an entry register value cannot be observed by the callee.
The complete owner, frame, direct calls and literal identities are checked
separately. Ordinary callees retain the existing conditional ABI boundary.
"""
import hashlib
import json
import struct

SELECTOR = 'incoming-scratch-overwrite-ordinary-v1'
SCHEMA = 'thumb-incoming-scratch-overwrite-ordinary-v1'
MAX_BYTES = 512


def sha(data):
    return hashlib.sha256(data).hexdigest()


def prefix_effects(instruction):
    """Only an authenticated straight-line Thumb entry prefix can kill aliases."""
    import match
    if instruction.size != 2:
        raise ValueError('scratch overwrite prefix excludes calls and unknown effects')
    word = int.from_bytes(instruction.bytes, 'little')
    reg = lambda n: match.ARM_REG_R0 + n
    reads, writes = set(), set()
    if word & 0xFE00 == 0xB400:  # PUSH low registers and optional LR
        reads = {reg(n) for n in range(8) if word & (1 << n)}
        if word & 0x100:
            reads.add(match.ARM_REG_LR)
        reads.add(match.ARM_REG_SP)
        writes.add(match.ARM_REG_SP)
    elif word & 0xE000 == 0 and word & 0x1800 != 0x1800:
        reads.add(reg((word >> 3) & 7))
        writes.add(reg(word & 7))
    elif word & 0xF800 == 0x1800:
        reads.add(reg((word >> 3) & 7))
        if not word & 0x400:
            reads.add(reg((word >> 6) & 7))
        writes.add(reg(word & 7))
    elif word & 0xF800 == 0x2000:  # MOVS immediate, no input flags
        writes.add(reg((word >> 8) & 7))
    else:
        raise ValueError('scratch overwrite prefix excludes memory, control and unknown effects')
    decoded_reads, decoded_writes = instruction.regs_access()
    if set(decoded_reads) - {match.ARM_REG_CPSR} != reads or \
            set(decoded_writes) - {match.ARM_REG_CPSR} != writes:
        raise ValueError('scratch overwrite prefix has inconsistent implicit effects')
    return reads, writes


def authenticate_ordinary(rom, mapping, index, objects, caller, size, target):
    """Reuse existing complete-owner and ordinary-call guards, never a leaf exemption."""
    import match
    import named_data_buffer_profile as named
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    entries = json.loads(mapping)
    match.function_address_target(f'func_{target:08X}', entries,
                                  caller, size, len(rom))
    row = next(row for row in entries if int(row['rom'], 16) == target)
    end = int(row['end'], 16)
    if not 0 < end - target <= MAX_BYTES:
        raise ValueError('scratch overwrite callee exceeds its complete-owner budget')
    data = rom[target-match.ROM_BASE:end-match.ROM_BASE]
    # This existing validator preserves legacy bounded numeric count hints;
    # the complete graph independently establishes the actual instruction count.
    named.validate_owner(data, target, rom, mapping, index)
    refinement = owner.refine(data, target, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, target, refinement)
    if branches or words:
        raise ValueError('scratch overwrite ordinary callee excludes local BL and switches')
    for destination in calls.values():
        match.function_address_target(f'func_{destination:08X}', entries,
                                      target, len(data), len(rom))
    verified = match.verify_leaf_instructions(data, target, True, calls)
    if {item.address for item in verified} != set(instructions):
        raise ValueError('scratch overwrite ordinary proof does not cover the complete callee')
    partition = graph.partition(data, target, refinement, instructions, words)
    object_names = match.parse_data_symbols(objects)
    bindings = {'calls': [[site-target, f'func_{callee:08X}']
                         for site, callee in sorted(calls.items())], 'data': [], 'functions': []}
    address_words = set()
    for word in partition['words']:
        value, offset = word['value'], word['address'] - target
        if not word['load_sites'] or not 0x02000000 <= value < 0x09000000:
            continue
        names = sorted(name for name, address in object_names.items() if address == value)
        if not names:
            raise ValueError('scratch overwrite literal requires genuine mapped object identity')
        address_words.add(offset)
        bindings['data'].append([offset, names[0], 0])
    _, literals = match.function_address_bindings(data, target, rom,
        mapping, objects, bindings, allow_empty_functions=True)
    match.verify_data_literals(instructions.values(), target, literals)
    if set(literals) != address_words:
        raise ValueError('scratch overwrite typed literals do not cover every actual address word')
    record = {'schema': SCHEMA, 'address': target, 'end': end,
        'body_sha256': sha(data), 'instructions': len(instructions),
        'partition': partition, 'calls': bindings['calls'], 'bindings': bindings,
        'ordinary_boundary': 'conditional ordinary ARM ABI; no transitive effect or termination proof',
        **{name+'_sha256': sha(value) for name,value in (('rom',rom),('mapping',mapping),('index',index),('objects',objects))}}
    return instructions, edges, record


class IncomingScratchOverwriteProof:
    """One exact caller and an explicit subset of its original direct BL sites."""
    def __init__(self, rom, mapping, index, objects, caller, size, calls, sites, *, policy):
        import match
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        if policy != SELECTOR or type(policy) is not str:
            raise ValueError('scratch overwrite requires its explicit versioned policy')
        if any(type(value) is not bytes for value in (rom, mapping, index, objects)):
            raise ValueError('scratch overwrite requires immutable current input snapshots')
        self.rom, self.mapping, self.index, self.objects = rom, mapping, index, objects
        self.caller, self.size = caller, size
        self.calls, self.sites = dict(calls), dict(sites)
        if not self.sites or any(self.calls.get(site) != target for site, target in self.sites.items()):
            raise ValueError('scratch overwrite sites must be exact selected original calls')
        data = rom[caller - match.ROM_BASE:caller - match.ROM_BASE + size]
        owner.validate_span(data, caller, rom, mapping, index)
        refinement = owner.refine(data, caller, mapping)
        self.instructions, self.edges, branches, reached, words = graph.graph(data, caller, refinement)
        if branches or words or reached != self.calls:
            raise ValueError('scratch overwrite caller differs from its complete ordinary CFG')
        self.identities = self._identities()
        self.dependencies, self.observations = {}, []

    def _identities(self):
        return {name + '_sha256': sha(getattr(self, name))
                for name in ('rom', 'mapping', 'index', 'objects')}

    def bind_caller(self, instructions, edges, address, calls):
        if self._identities() != self.identities or address != self.caller or calls != self.calls or \
                edges != self.edges or set(instructions) != set(self.instructions) or any(
                    bytes(item.bytes) != bytes(self.instructions[site].bytes)
                    for site, item in instructions.items()):
            raise ValueError('scratch overwrite requires the exact authenticated caller CFG and inputs')

    def ordinary(self, target):
        return authenticate_ordinary(self.rom, self.mapping, self.index, self.objects,
                                     self.caller, self.size, target)

    def check_call(self, site, target, aliases, stack, pointer_slots, initialized):
        import match
        if self._identities() != self.identities or self.sites.get(site) != target:
            raise ValueError('scratch overwrite call or input snapshots are stale or unbound')
        selected = set(aliases) & set(match.CALLER_CLOBBERED)
        if not selected or selected - {match.ARM_REG_R0+n for n in range(4)}:
            raise ValueError('scratch overwrite requires actual low incoming scratch aliases')
        for register in selected:
            values = aliases[register]
            if not values or any(type(offset) is not int or live is not True or
                    not -4*len(stack) <= offset < 0 or
                    stack[(offset + 4*len(stack))//4][0] != 'local'
                    for offset, live in values):
                raise ValueError('scratch overwrite incoming alias is unknown, expired or outside live locals')
        # Pointer slots and initializedness are facts owned by the caller. They
        # are retained exactly, rather than cleared or promoted by this proof.
        snapshot = repr((aliases, stack, pointer_slots, initialized))
        instructions, edges, record = self.ordinary(target)
        live, killed, prefix = set(selected), {}, []
        current = target
        while live:
            instruction = instructions[current]
            reads, writes = prefix_effects(instruction)
            if reads & live:
                raise ValueError('scratch overwrite observes incoming alias before full kill')
            for register in live & writes:
                killed[register] = current
            live -= writes
            prefix.append([current-target, bytes(instruction.bytes).hex()])
            if live:
                if edges[current] != (current + instruction.size,):
                    raise ValueError('scratch overwrite requires an unconditional entry-prefix kill')
                current += instruction.size
                if current not in instructions:
                    raise ValueError('scratch overwrite lacks a complete prior-to-use kill')
        if snapshot != repr((aliases, stack, pointer_slots, initialized)):
            raise ValueError('scratch overwrite changed caller pointer-slot or initialization facts')
        self.dependencies[target] = record
        self.observations.append({'site': site, 'target': target, 'prefix': prefix,
            'killed': [[instructions[target].reg_name(register), killed[register]]
                       for register in sorted(selected)],
            'caller_state_preserved': True})

    def manifest(self):
        return {'schema': SCHEMA, 'policy': SELECTOR, 'caller': self.caller,
                'callees': [self.dependencies[target] for target in sorted(self.dependencies)],
                'observations': self.observations, **self.identities}
