"""Finite acyclic manager-load paths into one conditional scheduler call.

Every syntactic entry-to-call path must establish the same three-stage shape,
without asserting equal loaded values across paths or memory readability.
"""
import hashlib
from pathlib import Path

import match
import scheduler_entry_profile as entry

SELECTOR = 'conditional-scheduler-manager-paths-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR
MAX_PATHS = 4096
MAX_STEPS = 65536
MAX_DEPTH = 4096


def bind(data, address, ins, edges, calls):
    entry.require(len(calls) == 1 and set(calls.values()) == {entry.DIRECT},
                  'manager paths contract requires one direct scheduler call')
    site = next(iter(calls))
    predecessors = {}
    for source, targets in edges.items():
        for target in targets:
            predecessors.setdefault(target, []).append(source)
    entry.require(address in ins and site in ins and not predecessors.get(address),
                  'manager paths require a unique entry origin')
    pending = [(site, (site,))]
    paths, steps = [], 0
    while pending:
        current, reverse = pending.pop()
        steps += 1
        entry.require(steps <= MAX_STEPS, 'manager paths traversal budget exceeded')
        if current == address:
            paths.append(tuple(reversed(reverse)))
            entry.require(len(paths) <= MAX_PATHS, 'manager paths count budget exceeded')
            continue
        before = predecessors.get(current, ())
        entry.require(before, 'manager path lacks an entry origin')
        for previous in before:
            entry.require(previous in ins and previous not in reverse,
                          'manager paths require finite acyclic instruction predecessors')
            entry.require(len(reverse) < MAX_DEPTH, 'manager paths depth budget exceeded')
            pending.append((previous, reverse + (previous,)))
            entry.require(len(pending) <= MAX_STEPS,
                          'manager paths traversal budget exceeded')

    low = set(range(match.ARM_REG_R0, match.ARM_REG_R0 + 8))

    def load(instruction, destination):
        operands = instruction.operands
        entry.require(instruction.mnemonic == 'ldr' and instruction.size == 2
                      and len(operands) == 2 and operands[0].type == match.ARM_OP_REG
                      and operands[0].reg == destination
                      and operands[1].type == match.ARM_OP_MEM
                      and not operands[1].mem.index and not instruction.writeback,
                      'manager paths require immediate word loads at every first definition')
        return operands[1].mem

    chains = {}
    for path in paths:
        entry.require(all(node not in calls and ins[node].mnemonic not in ('bl', 'blx')
                          for node in path[:-1]),
                      'manager path provenance cannot cross a call')

        def definition(stop, register):
            for position in range(stop - 1, -1, -1):
                instruction = ins[path[position]]
                if register in instruction.regs_access()[1]:
                    return position, instruction
            raise ValueError('manager path register has no entry definition')

        final_position, final = definition(len(path) - 1, match.ARM_REG_R0)
        field = load(final, match.ARM_REG_R0)
        entry.require(field.base in low and 0 <= field.disp <= 124 and field.disp % 4 == 0,
                      'manager path field requires an aligned bounded Thumb word offset')
        pointer_position, pointer = definition(final_position, field.base)
        first = load(pointer, field.base)
        entry.require(first.base in low and first.disp == 0,
                      'manager path pointer requires a zero-offset first dereference')
        _, literal = definition(pointer_position, first.base)
        origin = load(literal, first.base)
        entry.require(origin.base == match.ARM_REG_PC,
                      'manager path pointer origin must be one PC-relative literal')
        offset = ((literal.address + 4) & ~3) + origin.disp - address
        entry.require(0 <= offset <= len(data) - 4 and (address + offset) % 4 == 0,
                      'manager path literal must be a complete aligned owner word')
        chain = dict(literal_offset=offset, load_site=literal.address,
                     pointer_load_site=pointer.address, dereference_site=final.address,
                     dereference_count=2, literal_register=first.base,
                     pointer_register=field.base, field_offset=field.disp)
        chains[(literal.address, pointer.address, final.address)] = chain
    entry.require(chains, 'manager paths require at least one authenticated chain')
    return dict(address=entry.DIRECT, kind='direct-named-manager-paths',
                descriptor_register=3, dependencies=(entry.DIRECT,),
                manager_paths=[chains[key] for key in sorted(chains)],
                entry_to_call_paths=len(paths))


def check_call(proof, address, aliases, stack, slots, *, site):
    return entry.check_call(proof, address, aliases, stack, slots, site=site)


def check_bindings(manifest, bindings):
    for chain in manifest['entry']['manager_paths']:
        rows = [row for row in bindings['data'] if row[0] == chain['literal_offset']]
        entry.require(len(rows) == 1 and len(rows[0]) == 3 and rows[0][2] == 0,
                      'every manager path literal requires one typed zero-addend named data relocation')


def manifest(proof):
    result = entry.manifest(proof)
    result['schema'] = SCHEMA
    result['entry_source_sha256'] = result['source_sha256']
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['assumptions'][-1] = (
        'On each actual path, the recorded typed named literal addresses a readable aligned word. '
        'The pointer actually read from that word plus that chain\'s recorded field offset '
        'addresses another readable aligned word without address wraparound; both storage words '
        'are separate from every caller stack word. Their values are those seen by the recorded '
        'ordered loads; intervening writes do not imply unchanged memory or equal values across paths. '
        'No initialization, allocation, lifetime or readability follows from literal identity. '
        'The second loaded value on the actual path is a valid scheduler manager separate from '
        'every caller stack word. The pinned func_08005954 reads its fifth argument from the caller '
        'outgoing word at SP (ldr r6,[sp,#0x38] after its 56-byte frame). That parent word holds '
        'no tracked local pointer; its initialization is not checked. No other caller private or '
        'saved word is read through SP.')
    result['manager_memory_access_proved'] = False
    result['manager_values_equal_across_paths_proved'] = False
    return result
