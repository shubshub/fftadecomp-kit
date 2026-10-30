"""Inventory-only framed UDIV/MOD with one explicit read-only incoming ABI word."""
import argparse
import json
from pathlib import Path

import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations
import readonly_entry_stack_profile as entry_stack
import zero_aware_unsigned_quotient_inventory as core

SELECTOR = 'zero-aware-unsigned-quotient-framed-entry-word-inventory-v1'
SCHEMA = 'thumb-canonical-zero-aware-unsigned-quotient-framed-entry-word-inventory-v1'
bind_calls = core.bind_calls


def runtime_frames(rom, mapping, observed):
    """Prove each canonical callee's frame stays below the caller SP."""
    from capstone.arm import ARM_REG_R4, ARM_REG_R11
    closure = dict(observed['native_runtime_closure'])
    if set(closure) != {0x0814274C, core.UDIV, core.remainder.remainder.ADDRESS}:
        raise ValueError('framed unsigned inventory requires its exact complete runtime closure')
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11 + 1))
    proven = {}
    for address, end in ((0x0814274C, 0x0814274E), (core.UDIV, 0x08142B28),
                         (core.remainder.remainder.ADDRESS, 0x08142A1E)):
        body = rom[address - match.ROM_BASE:end - match.ROM_BASE]
        refinement = owner.refine(body, address, mapping)
        instructions, edges, branches, calls, words = graph.graph(body, address, refinement)
        if branches or words or any(target not in proven for target in calls.values()) or \
                closure[address]['writes'] or closure[address]['stack_reads']:
            raise ValueError('framed unsigned runtime has unproved caller-memory effects')
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
            call_preservation={site: preserved for site in calls})
        if restored['returns'] != closure[address]['returns']:
            raise ValueError('framed unsigned runtime return coverage differs')
        proven[address] = {'frame': restored,
            'maximum_additional_stack_bytes': restored['maximum_frame_bytes'] + max(
                (proven[target]['maximum_additional_stack_bytes'] for target in calls.values()), default=0),
            'caller_memory_writes': [], 'caller_stack_reads': [],
            'restores': 'r4-r11,sp,entry-lr'}
    return [[site, proof] for site, proof in sorted(proven.items())]


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('framed unsigned inventory requires its explicit entry-word selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('framed unsigned inventory requires immutable exact ROM/index inputs')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if calls != actual_calls or branches or words or \
            not any((match.thumb_stack_adjustment(item) or 0) < 0 for item in instructions.values()):
        raise ValueError('framed unsigned inventory requires its exact allocated direct-call CFG')
    from software_double_profile import indices, span_record
    indexed_entries, rows = indices(mapping, index)
    if span_record(address, address + len(data), indexed_entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('framed unsigned caller count differs from its complete native CFG')
    partition = graph.partition(data, address, refinement, instructions, words)
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    observed = {}
    sites = core.prepare(data, address, calls, (rom, mapping, index, bindings, observed, core.SELECTOR))
    native_frames = runtime_frames(rom, mapping, observed)
    core.prove_operands(data, address, instructions, edges, sites, observed)
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True,
        entry_stack_policy={'schema': entry_stack.SCHEMA, 'words': [0]})
    if not restored['entry_stack']['reads']:
        raise ValueError('framed unsigned entry-word inventory requires an actual incoming word read')
    observed.update(schema=SCHEMA, selector=SELECTOR, frame=restored, partition=partition,
        native_runtime_frames=native_frames, instructions=len(instructions), address=address, end=address+len(data),
        entry_stack_contract=entry_stack.CONTRACT,
        runtime_stack_policy='canonical UDIV/MOD access only their proved frames below caller SP',
        ordinary_call_stack_bound=None,
        ordinary_call_stack_premise='conditional returning-call ABI only; no ordinary callee stack bound',
        ordinary_callee_native_proof=False,
        calls=[[site-address, name] for site, name in sorted(bindings.items())],
        runtime_calls=[[site-address, name] for site, name in sorted(bindings.items()) if name in core.OPERATIONS],
        body_sha256=core.remainder.sha(data), mapping_sha256=core.remainder.sha(mapping),
        index_sha256=core.remainder.sha(index), ROM_sha256=core.remainder.sha(rom), complete_native_proof=True)
    if manifest is not None and core.remainder.text(manifest) != core.remainder.text(observed):
        raise ValueError('framed unsigned inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('framed unsigned inventory requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(rows[0]['end'], 16)-match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(core.remainder.text(observed))


if __name__ == '__main__':
    main()
