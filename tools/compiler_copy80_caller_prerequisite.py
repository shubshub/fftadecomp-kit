"""Actual caller-prefix provenance for the conditional aligned copy80 helper.

No compiler binding or complete caller admission is supplied here. The prefix
is restricted to acyclic, call-free paths; all syntactic paths reaching the copy
must derive the same original entry argument, named point and fixed frame.
"""
import hashlib
from pathlib import Path

import compiler_copy80_prerequisite as helper
import match
import named_data_buffer_profile as buffers
import owner_graph_profile as graph
from local_rom_halfword_table_profile import require

SCHEMA = 'conditional-copy80-caller-prefix-prerequisite-v1'


def register(instruction, operand):
    require(operand.type == match.ARM_OP_REG, 'register operand required')
    name = instruction.reg_name(operand.reg)
    aliases = {'sb': 9, 'sl': 10, 'fp': 11, 'ip': 12, 'sp': 13, 'lr': 14, 'pc': 15}
    return aliases[name] if name in aliases else int(name[1:])


def immediate_or_register(instruction, operand, registers):
    if operand.type == match.ARM_OP_IMM:
        return ('constant', operand.imm & 0xFFFFFFFF)
    return registers[register(instruction, operand)]


def add(value, amount):
    require(amount is None or amount[0] != 'stack',
            'stack alias used as an arithmetic addend is unsupported')
    if value is None or amount is None or amount[0] != 'constant':
        require(value is None or value[0] != 'stack', 'variable stack alias arithmetic is unsupported')
        return None
    n = amount[1]
    if n & 0x80000000:
        n -= 0x100000000
    if value[0] == 'constant':
        return ('constant', (value[1]+n) & 0xFFFFFFFF)
    if value[0] == 'entry':
        return ('entry', value[1], value[2]+n)
    if value[0] == 'literal':
        return (*value[:3], value[3]+n)
    if value[0] == 'stack':
        return ('stack', value[1]+n)
    return None


def advance(instruction, state, data, address):
    registers, saves, memory = list(state[0]), list(state[1]), list(state[2])
    op, operands = instruction.mnemonic, instruction.operands
    if op == 'push':
        require(registers[13] is not None and registers[13][0] == 'stack', 'fixed stack required')
        selected = [register(instruction, item) for item in operands]
        require(selected == sorted(set(selected)) and all(r < 13 or r == 14 for r in selected),
                'canonical fixed register save required')
        low = registers[13][1]-4*len(selected)
        require(not ({offset for offset, _ in saves} & set(range(low, registers[13][1], 4))),
                'prefix cannot overwrite an existing saved word')
        saves.extend((low+4*i, registers[r]) for i, r in enumerate(selected))
        registers[13] = ('stack', low)
    elif op in ('mov', 'movs'):
        registers[register(instruction, operands[0])] = immediate_or_register(instruction, operands[1], registers)
    elif op in ('add', 'adds', 'sub', 'subs'):
        dest = register(instruction, operands[0])
        left = registers[dest] if len(operands) == 2 else immediate_or_register(instruction, operands[1], registers)
        right = immediate_or_register(instruction, operands[-1], registers)
        if op.startswith('sub'):
            right = ('constant', -right[1] & 0xFFFFFFFF) if right and right[0] == 'constant' else None
        registers[dest] = add(left, right)
    elif op == 'lsls':
        dest = register(instruction, operands[0])
        value = immediate_or_register(instruction, operands[1], registers)
        shift = immediate_or_register(instruction, operands[2], registers)
        require(value is None or value[0] != 'stack', 'prefix cannot shift a stack pointer')
        require(shift is not None and shift[0] == 'constant' and shift[1] < 32, 'fixed shift required')
        registers[dest] = ('constant', value[1] << shift[1] & 0xFFFFFFFF) if value and value[0] == 'constant' else None
    elif op in ('ldr', 'ldrb', 'ldrh', 'ldrsb', 'ldrsh', 'str', 'strb', 'strh'):
        require(len(operands) == 2 and operands[1].type == match.ARM_OP_MEM, 'simple prefix memory access required')
        base = instruction.reg_name(operands[1].mem.base)
        if op == 'ldr' and base == 'pc':
            offset = ((instruction.address+4) & ~3)+operands[1].mem.disp-address
            require(0 <= offset <= len(data)-4, 'prefix literal lies outside complete owner')
            value = int.from_bytes(data[offset:offset+4], 'little')
            registers[register(instruction, operands[0])] = ('literal', value, offset, 0)
        else:
            require(base != 'pc' and not operands[1].mem.index, 'unindexed ordinary prefix access required')
            base_reg = {'sp': 13, 'sb': 9, 'sl': 10, 'fp': 11, 'ip': 12}.get(base)
            if base_reg is None:
                require(base.startswith('r') and base[1:].isdigit(), 'ordinary prefix base register required')
                base_reg = int(base[1:])
            value = registers[base_reg]
            require(value is None or value[0] != 'stack', 'prefix stack accesses need a separate proof')
            memory.append(instruction.address-address)
            if op.startswith('ldr'):
                registers[register(instruction, operands[0])] = None
            else:
                stored = registers[register(instruction, operands[0])]
                require(stored is None or stored[0] != 'stack', 'prefix cannot store a local stack pointer')
    elif op not in ('cmp', 'tst', 'b', 'beq', 'bne', 'bgt', 'bge', 'blt', 'ble', 'bhi', 'bhs', 'blo', 'bls'):
        raise ValueError(f'unsupported copy prefix instruction: {op}')
    require(registers[13] is not None and registers[13][0] == 'stack' and
            -4096 <= registers[13][1] <= 0 and registers[13][1] % 4 == 0,
            'prefix requires a bounded fixed caller frame')
    return tuple(registers), tuple(saves), tuple(memory)


def verify(data, address, rom, mapping, index, objects):
    import owner_admission_profile as owner

    require(all(type(raw) is bytes for raw in (data, rom, mapping, index, objects)) and
            type(address) is int, 'immutable original inputs required')
    buffers.validate_owner(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
    partition = graph.partition(data, address, refinement, instructions, words)
    require(not branches and not words, 'copy prefix excludes local long branches and switch words')
    candidates = [(site, target) for site, target in calls.items() if hashlib.sha256(
        rom[target-match.ROM_BASE:target-match.ROM_BASE+98]).hexdigest() == helper.COPY_SHA256]
    require(len(candidates) == 1, 'one actual canonical copy-helper call required')
    site, target = candidates[0]
    proof = helper.verify_helper(target, rom, mapping, index)
    predecessors = {key: set() for key in instructions}
    for source, destinations in edges.items():
        for destination in destinations:
            if destination in predecessors:
                predecessors[destination].add(source)
    ancestors, pending = set(), [site]
    while pending:
        node = pending.pop()
        if node not in ancestors:
            ancestors.add(node)
            pending.extend(predecessors[node])
    require(address in ancestors and len(ancestors) <= 256, 'bounded reachable copy prefix required')
    require(not (set(calls) & (ancestors-{site})), 'copy prefix cannot cross another call')
    order, remaining = [], set(ancestors)
    while remaining:
        ready = sorted(node for node in remaining if not (predecessors[node] & remaining))
        require(ready, 'cyclic copy prefix requires a separate proof')
        order.extend(ready)
        remaining.difference_update(ready)
    registers = tuple(('entry', r, 0) for r in range(13))+(('stack', 0), ('entry_return',), None)
    states = {address: {(registers, (), ())}}
    for node in order:
        require(node in states and len(states[node]) <= 128, 'copy prefix state budget exceeded')
        if node == site:
            break
        for state in states[node]:
            after = advance(instructions[node], state, data, address)
            for destination in edges[node]:
                if destination in ancestors:
                    states.setdefault(destination, set()).add(after)
    summaries = set()
    names = match.parse_data_symbols(objects)
    for registers, saves, memory in states[site]:
        require(registers[0] == ('entry', 2, 100) and registers[2] == ('constant', 80),
                'copy requires actual entry_R2+100 destination and count80')
        source = registers[1]
        require(source is not None and source[0] == 'literal' and source[3] == 0 and source[1] % 4 == 0,
                'copy source requires an actual aligned unchanged PC literal')
        identities = [name for name, point in names.items() if point == source[1]]
        require(len(identities) == 1, 'copy source requires one named point identity')
        summaries.add((source, identities[0], registers[13][1], saves, memory))
    require(len(summaries) == 1, 'copy prefix paths disagree on inputs, frame or effects')
    source, identity, stack, saves, memory = summaries.pop()
    require(all(stack <= offset and offset+4 <= 0 for offset, _ in saves), 'saved words leave caller frame')
    return dict(schema=SCHEMA, address=address, complete_bytes=len(data),
        native_instructions=len(instructions), partition=partition, call_site=site,
        source_point=source[1], source_identity=identity, source_literal_offset=source[2],
        destination=dict(entry_register=2, offset=100), count=80,
        caller_frame_bytes=-stack, combined_frame_bytes=-stack+12,
        prefix_instruction_offsets=[node-address for node in order if node != site],
        prefix_memory_offsets=list(memory), caller_saves=list(saves), helper=proof,
        conditions=proof['conditions']+[
            'entry_R2 is four-byte aligned and entry_R2+180 does not wrap',
            'ordinary prefix accesses are valid and prefix stores do not alias saved frame words',
            'caller instructions and literal words, helper code and active saves remain unchanged throughout the prefix except authenticated pushes',
            'complete caller suffix, actual lifetime/access conditions and original compiler transport remain separate'],
        complete_caller_admission=False, source_or_ELF_admission=False,
        physical_access_proved=False,
        input_pins={name: hashlib.sha256(raw).hexdigest() for name, raw in
            (('owner', data), ('rom', rom), ('mapping', mapping), ('index', index), ('objects', objects))},
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
