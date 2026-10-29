"""Explicit framed SHIFT inventory with exact MOD stack and save effects."""
import argparse
import json
from pathlib import Path

import zero_aware_remainder_ordinary_inventory as ordinary
import zero_aware_remainder_shift_inventory as shift

SELECTOR = 'zero-aware-remainder-framed-shift-inventory-v1'
SCHEMA = 'thumb-canonical-zero-aware-remainder-framed-shift-inventory-v1'
bind_calls = ordinary.bind_calls
prove_operands = shift.prove_operands


def runtime_frames(rom, mapping, observed):
    """Compose existing exact runtime closure with its restoring frame proof."""
    from capstone.arm_const import ARM_REG_R4, ARM_REG_R11
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame

    closure = dict(observed['native_runtime_closure'])
    if set(closure) != {0x0814274C, ordinary.pure.remainder.ADDRESS}:
        raise ValueError('framed remainder requires its exact complete runtime closure')
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11 + 1))
    proven = {}
    for address, end in ((0x0814274C, 0x0814274E),
                         (ordinary.pure.remainder.ADDRESS, 0x08142A1E)):
        data = rom[address - 0x08000000:end - 0x08000000]
        refinement = owner.refine(data, address, mapping)
        instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
        if branches or words or any(target not in proven for target in calls.values()) or \
                closure[address]['writes'] or closure[address]['stack_reads']:
            raise ValueError('framed remainder runtime has unproved caller-memory effects')
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
            call_preservation={site: preserved for site in calls})
        if restored['returns'] != closure[address]['returns']:
            raise ValueError('framed remainder runtime return coverage differs')
        nested = max((proven[target]['maximum_additional_stack_bytes']
                      for target in calls.values()), default=0)
        proven[address] = {'frame': restored,
            'maximum_additional_stack_bytes': restored['maximum_frame_bytes'] + nested,
            'caller_memory_writes': [], 'caller_stack_reads': [],
            'restores': 'r4-r11,sp,entry-lr'}
    return [[address, proof] for address, proof in sorted(proven.items())]


def prepare(data, address, calls, context):
    if type(context) is not tuple or len(context) != 6 or context[5] != SELECTOR:
        raise ValueError('framed remainder requires its explicit fresh inventory context')
    runtime = shift.prepare(data, address, calls, context[:5] + (shift.SELECTOR,))
    context[4].update(schema=SCHEMA, selector=SELECTOR,
        native_runtime_frames=runtime_frames(context[0], context[1], context[4]))
    return runtime


def finish(data, address, calls, context, verified):
    import match
    verified = list(verified)
    shift.finish(data, address, calls, context, verified)
    if not any((match.thumb_stack_adjustment(item) or 0) < 0 for item in verified):
        raise ValueError('framed remainder requires an allocated caller stack frame')
    frames = dict(context[4]['native_runtime_frames'])
    context[4].update(caller_frame_policy='exact allocated locals, saved slots, SP and entry-LR restoration',
        runtime_stack_policy='canonical MOD accesses only its own proved frame below caller SP',
        maximum_MOD_stack_bytes_below_caller_SP=
            frames[ordinary.pure.remainder.ADDRESS]['maximum_additional_stack_bytes'],
        ordinary_call_stack_bound=None,
        ordinary_call_stack_premise='conditional returning-call ABI only; no ordinary callee stack bound',
        external_call_policy='complete exact canonical MOD frame and closure plus conditional ordinary returning-call ABI')


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    if selector != SELECTOR:
        raise ValueError('framed remainder requires its explicit inventory-only selector')
    observed = {}
    verified = match.verify_leaf_instructions(data, address, True, calls,
        remainder_framed_shift_inventory_context=(rom, mapping, index, bindings, observed, selector))
    if manifest is not None and ordinary.pure.text(manifest) != ordinary.pure.text(observed):
        raise ValueError('framed remainder inventory manifest differs from fresh native proof')
    return observed, verified


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    parser.add_argument('--rom', required=True, type=Path)
    parser.add_argument('--mapping', required=True, type=Path)
    parser.add_argument('--index', required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('framed remainder inventory requires one exact mapped owner')
    data = rom[args.address - 0x08000000:int(rows[0]['end'], 16) - 0x08000000]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    manifest, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(ordinary.pure.text(manifest))


if __name__ == '__main__':
    main()
