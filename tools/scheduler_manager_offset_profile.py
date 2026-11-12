"""Conditional scheduler manager reached through two recorded word loads.

The first load dereferences a typed named literal. The second uses an aligned
constant field offset. Register provenance is checked backwards on one finite
straight-line path; readability and separation remain explicit premises.
"""
import hashlib
from pathlib import Path

import match
import scheduler_entry_profile as entry

SELECTOR = 'conditional-scheduler-manager-offset-v1'
SCHEMA = 'elf-symbol-thumb-' + SELECTOR


def bind(data, address, ins, edges, calls):
    entry.require(len(calls) == 1 and set(calls.values()) == {entry.DIRECT},
                  'manager offset contract requires one direct scheduler call')
    site = next(iter(calls))
    predecessors = {}
    for source, targets in edges.items():
        for target in targets:
            predecessors.setdefault(target, []).append(source)

    def definition(current, register):
        seen = {current}
        while True:
            before = predecessors.get(current, [])
            entry.require(len(before) == 1 and list(edges[before[0]]) == [current]
                          and before[0] not in seen and before[0] in ins,
                          'manager offset requires a finite straight-line load chain')
            current = before[0]
            seen.add(current)
            instruction = ins[current]
            entry.require(current not in calls and instruction.mnemonic not in ('bl', 'blx'),
                          'manager offset provenance cannot cross a call')
            if register in instruction.regs_access()[1]:
                return instruction

    def load(instruction, destination):
        operands = instruction.operands
        entry.require(instruction.mnemonic == 'ldr' and instruction.size == 2
                      and len(operands) == 2 and operands[0].type == match.ARM_OP_REG
                      and operands[0].reg == destination
                      and operands[1].type == match.ARM_OP_MEM
                      and not operands[1].mem.index,
                      'manager offset requires exactly two immediate word dereferences')
        return operands[1].mem

    final = definition(site, match.ARM_REG_R0)
    field = load(final, match.ARM_REG_R0)
    low = set(range(match.ARM_REG_R0, match.ARM_REG_R0 + 8))
    entry.require(field.base in low and 0 <= field.disp <= 124 and field.disp % 4 == 0,
                  'manager field requires an aligned bounded Thumb word offset')
    pointer = definition(final.address, field.base)
    first = load(pointer, field.base)
    entry.require(first.base in low and first.disp == 0,
                  'manager pointer requires a zero-offset first dereference')
    literal = definition(pointer.address, first.base)
    origin = load(literal, first.base)
    entry.require(origin.base == match.ARM_REG_PC,
                  'manager pointer origin must be one PC-relative literal')
    offset = ((literal.address + 4) & ~3) + origin.disp - address
    entry.require(0 <= offset <= len(data) - 4 and (address + offset) % 4 == 0,
                  'manager literal must be a complete aligned owner word')
    return dict(address=entry.DIRECT, kind='direct-named-manager-offset',
                descriptor_register=3, dependencies=(entry.DIRECT,),
                manager=dict(literal_offset=offset, load_site=literal.address,
                             pointer_load_site=pointer.address,
                             dereference_site=final.address, dereference_count=2,
                             literal_register=first.base, pointer_register=field.base,
                             field_offset=field.disp))


def check_call(proof, address, aliases, stack, slots, *, site):
    return entry.check_call(proof, address, aliases, stack, slots, site=site)


def check_bindings(manifest, bindings):
    entry.check_bindings(manifest, bindings)


def manifest(proof):
    result = entry.manifest(proof)
    result['schema'] = SCHEMA
    result['entry_source_sha256'] = result['source_sha256']
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    offset = result['entry']['manager']['field_offset']
    result['assumptions'][-1] = (
        'The recorded typed named literal addresses a readable aligned word. '
        f'The pointer actually read from that word plus the recorded field offset {offset} '
        'addresses another readable aligned word without address wraparound; both storage '
        'words are separate from every caller stack word. Their values are the values seen '
        'by the recorded ordered loads; intervening writes do not imply unchanged memory. '
        'No initialization, allocation, lifetime or readability follows from literal identity. '
        'The second loaded value is a valid scheduler manager separate from every caller '
        'stack word. The pinned func_08005954 reads its fifth argument from the caller '
        'outgoing word at SP (ldr r6,[sp,#0x38] after its 56-byte frame). That parent word '
        'holds no tracked local pointer; its initialization is not checked. No other caller '
        'private or saved word is read through SP.')
    result['manager_memory_access_proved'] = False
    return result
