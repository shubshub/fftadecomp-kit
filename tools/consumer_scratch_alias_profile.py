"""Inventory-only ignored R2 leaf plus exact caller overwrite-before-use proof.

No incoming alias is erased solely by a calling convention. An authenticated
read-only leaf must not observe entry R2, and every complete caller successor
path must overwrite it before any read, call or return. Local memory state is
preserved, including possible pointer taint. No memory readability or numeric
result theorem follows from an unknown scalar load.
"""
import json
from pathlib import Path

import ignored_leaf_alias_profile as ignored

SELECTOR = 'mutable-four-local-word-alias-slot-halfword-scalar-slot-consumer-scratch-v1'
SCHEMA = 'thumb-ignored-leaf-consumer-r2-scratch-v1'
MAX_PREFIX_SITES = 128


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def scalar_read_effects(instruction):
    """Existing closed leaf effects plus one authenticated unknown LDRSH."""
    import match
    import zero_index_stack_profile as zero
    try:
        return ignored.effects(instruction)
    except ValueError:
        decoded = zero.signed_load(instruction)
        if decoded is None or decoded[2] != 2:
            raise ValueError('consumer leaf has an unsupported instruction effect') from None
        read, written = set(decoded[:2]), {instruction.operands[0].reg}
        allowed = set(range(match.ARM_REG_R0, match.ARM_REG_R0 + 4))
        actual_read, actual_written = instruction.regs_access()
        if (read | written) - allowed or set(actual_read) != read or set(actual_written) != written:
            raise ValueError('consumer leaf signed load has inconsistent or non-scratch effects')
        return read, written


def consumer_effects(instruction):
    """Closed consumer prefix, including actual non-SP high-register ADD."""
    import match
    from capstone.arm_const import ARM_OP_REG
    raw = int.from_bytes(instruction.bytes, 'little')
    if instruction.size == 2 and raw & 0xFF00 == 0x4400:
        destination = match.ARM_REG_R0 + (raw & 7) + ((raw >> 4) & 8)
        source = match.ARM_REG_R0 + ((raw >> 3) & 15)
        read, written = {destination, source}, {destination}
        allowed = set(range(match.ARM_REG_R0, match.ARM_REG_R12 + 1))
        ops = instruction.operands
        actual_read, actual_written = instruction.regs_access()
        if instruction.mnemonic != 'add' or len(ops) != 2 or \
                any(op.type != ARM_OP_REG or op.shift.type or op.shift.value or op.subtracted for op in ops) or \
                tuple(op.reg for op in ops) != (destination, source) or \
                (read | written) - allowed or set(actual_read) != read or set(actual_written) != written:
            raise ValueError('consumer high-register ADD effects differ from exact bytes')
        return read, written
    return ignored.effects(instruction)


def signature(instructions, edges):
    return ([[site, bytes(item.bytes).hex(), item.mnemonic, item.op_str,
              [list(registers) for registers in item.regs_access()]]
             for site, item in sorted(instructions.items())],
            [[site, list(destinations)] for site, destinations in sorted(edges.items())])


class ConsumerScratchAliasProof(ignored.IgnoredLeafAliasProof):
    """One immutable complete caller, with fresh complete callee evidence."""
    instruction_effects = staticmethod(scalar_read_effects)

    def __init__(self, rom, mapping, index, objects, caller, size, calls):
        import match
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        if not all(type(value) is bytes for value in (rom, mapping, index, objects)):
            raise ValueError('consumer proof requires exact byte inputs including typed objects')
        super().__init__(rom, mapping, index, objects, caller, size, calls)
        data = rom[caller-match.ROM_BASE:caller-match.ROM_BASE+size]
        entries = owner.validate_span(data, caller, rom, mapping, index)
        refinement = owner.refine(data, caller, mapping)
        self.instructions, self.edges, branches, actual_calls, words = graph.graph(data, caller, refinement)
        if calls != actual_calls or branches or words:
            raise ValueError('consumer proof requires exact closed ordinary caller CFG and call sites')
        graph.partition(data, caller, refinement, self.instructions, words)
        row = next(row for row in entries if int(row['rom'], 16) == caller)
        rows = [line.split() for line in index.decode().splitlines()
                if line.split() and line.split()[0] == f'{caller:08X}']
        if row.get('instrs') != len(self.instructions) or len(rows) != 1 or \
                len(rows[0]) < 4 or int(rows[0][3]) != len(self.instructions):
            raise ValueError('consumer proof requires exact dual-index caller instruction counts')
        self.body = data
        self.cfg = signature(self.instructions, self.edges)
        self.input_identity = self.identity()
        self.source_identity = self.source_pins()
        self.checked = {}

    def source_pins(self):
        import match
        import owner_admission_profile as owner
        import owner_graph_profile as graph
        import zero_index_stack_profile as zero
        return {Path(module.__file__).name: ignored.sha(Path(module.__file__).read_bytes())
                for module in (ignored, match, match.armv4t, owner, graph, zero)} | {
                    Path(__file__).name: ignored.sha(Path(__file__).read_bytes())}

    def identity(self):
        return {'caller': self.caller, 'size': self.size,
            'rom_sha256': ignored.sha(self.rom), 'mapping_sha256': ignored.sha(self.mapping),
            'index_sha256': ignored.sha(self.index), 'objects_sha256': ignored.sha(self.objects),
            'calls': sorted(self.calls.items())}

    def fresh(self):
        if self.identity() != self.input_identity or self.source_pins() != self.source_identity or \
                signature(self.instructions, self.edges) != self.cfg:
            raise ValueError('consumer proof source, inputs or CFG changed')

    def bind_frame(self, instructions, edges, address, branches, calls):
        self.fresh()
        if address != self.caller or branches or calls != self.calls or signature(instructions, edges) != self.cfg:
            raise ValueError('consumer proof does not bind this exact complete caller frame/CFG/sites')

    def consumer(self, site):
        import match
        register = match.ARM_REG_R0 + 2
        visiting, seen, kills, inspected = set(), set(), set(), {}
        def walk(current):
            if current in visiting:
                raise ValueError('consumer live R2 path cycles before overwrite')
            if current in seen:
                return
            if len(inspected) >= MAX_PREFIX_SITES or current not in self.instructions:
                raise ValueError('consumer prefix exceeds closed CFG or bounded site budget')
            item = self.instructions[current]
            if current in self.calls or not self.edges[current]:
                raise ValueError('consumer forwards or returns live R2 before overwrite')
            read, written = consumer_effects(item)
            inspected[current] = {'site': current, 'bytes': bytes(item.bytes).hex(),
                'read': sorted(read), 'written': sorted(written), 'successors': list(self.edges[current])}
            if register in read:
                raise ValueError('consumer reads live R2 before overwrite')
            if register in written:
                kills.add(current)
            else:
                visiting.add(current)
                for destination in self.edges[current]:
                    walk(destination)
                visiting.remove(current)
            seen.add(current)
        walk(site + 4)
        return {'callsite': site, 'start': site+4, 'kill_sites': sorted(kills),
            'inspected': [inspected[key] for key in sorted(inspected)], 'all_paths_kill_before_read': True}

    def check_call(self, site, target, aliases, pointer_slots):
        import match
        self.fresh()
        register = match.ARM_REG_R0 + 2
        if self.calls.get(site) != target or set(aliases) & set(match.CALLER_CLOBBERED) != {register}:
            raise ValueError('consumer proof requires exact original BL and only incoming R2 scratch alias')
        import mutable_stack_index_profile as finite
        finite.offsets(aliases[register])
        data, native, instructions, edges, returns, accesses = self.leaf(target)
        pending, seen = [(target, True)], set()
        while pending:
            current, live = pending.pop()
            if (current, live) in seen:
                continue
            seen.add((current, live))
            read, written = accesses[current]
            if live and register in read:
                raise ValueError('consumer leaf observes incoming R2')
            live = live and register not in written
            pending.extend((successor, live) for successor in edges[current])
        # The read-only closed instruction set cannot mutate caller locals.
        # Possible pointer slots are retained, including unknown/dead taint.
        slots = [[offset, [list(value) for value in sorted(values)]]
                 for offset, values in sorted(pointer_slots.items())]
        record = {'callsite': site, 'target': target, 'register': 'r2',
            'callee': {'body_sha256': ignored.sha(data), 'bytes': len(data),
                'instructions': len(instructions), 'owner': native,
                'effects': [[pc, bytes(item.bytes).hex(), sorted(accesses[pc][0]), sorted(accesses[pc][1])]
                            for pc,item in sorted(instructions.items())],
                'entry_R2_never_observed': True, 'incoming_R2_may_be_preserved': True,
                'memory_writes': any(item.mnemonic == 'push' for item in instructions.values()),
                'caller_local_memory_writes': False,
                'private_save_frame_writes': [pc for pc,item in sorted(instructions.items()) if item.mnemonic == 'push'],
                'unknown_scalar_signed_halfword_read': any(item.mnemonic == 'ldrsh' for item in instructions.values())},
            'consumer': self.consumer(site), 'preserved_pointer_slots': slots}
        key = (site, text({str(r):sorted(values) for r,values in aliases.items()}), text(slots))
        self.checked[key] = record
        return {}

    def manifest(self):
        self.fresh()
        if not self.checked:
            raise ValueError('consumer proof requires an actual checked R2 scratch call')
        return {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
            'source_or_ELF_admission': False, 'caller_body_sha256': ignored.sha(self.body),
            'caller_CFG_sha256': ignored.sha(text(self.cfg).encode()),
            'input_identity': self.input_identity, 'producer_source_sha256': self.source_identity,
            'calls': [self.checked[key] for key in sorted(self.checked)],
            'ordinary_returning_ABI_conditional': True,
            'memory_readability_allocation_numeric_result_or_termination_theorem': False}
