"""Explicit formal-stack leaf-only inventory with exact reaching MOVS10 aliases."""
import argparse
import json
from pathlib import Path

import ordinary_formal_stack_callee_inventory as parent

SELECTOR = 'ordinary-formal-stack-leaf-only-movs10-inventory-v1'
SCHEMA = 'thumb-ordinary-formal-stack-leaf-only-movs10-inventory-v1'
LEAF = parent.LEAF
sha = parent.sha
text = parent.text


def bind_calls(calls, mapping, address, size, rom_size):
    if type(calls) is not dict or not calls or type(mapping) is not bytes or \
            any(type(value) is not int for value in (address, size, rom_size)) or \
            address % 2 or size <= 0 or not parent.match.ROM_BASE <= address < address+size <= parent.match.ROM_BASE+rom_size:
        raise ValueError('leaf-only inventory requires exact immutable ordinary call inputs')
    entries = json.loads(mapping)
    bound = {}
    for site, target in sorted(calls.items()):
        if type(site) is not int or type(target) is not int or site % 2 or \
                not address <= site <= address+size-4 or parent.thunks.reserved(target):
            raise ValueError('leaf-only inventory excludes thunks and malformed call boundaries')
        name = f'func_{target:08X}'
        actual = parent.match.function_address_target(name, entries, address, size, rom_size)
        rows = [row for row in entries if int(row['rom'], 16) == actual]
        end = int(rows[0]['end'], 16)
        if not actual < end <= parent.match.ROM_BASE+rom_size or actual < address+size and end > address or any(
                row is not rows[0] and int(row['rom'], 16) < end and int(row['end'], 16) > actual for row in entries):
            raise ValueError('leaf-only target requires unique nonoverlapping complete ownership')
        bound[site] = name
    if list(calls.values()).count(LEAF[0]) != 1 or parent.NOOP[0] in calls.values():
        raise ValueError('leaf-only inventory requires exactly one output leaf and no noop call')
    return bound


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('leaf-only MOVS10 inventory requires its explicit default-off selector')
    instructions, edges, actual_calls, partition = parent.complete(data, address, rom, mapping, index)
    if type(calls) is not dict or calls != actual_calls or type(bindings) is not dict or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('leaf-only bindings differ from all actual reached calls')
    entries, rows = parent.indices.indices(mapping, index)
    start, end, count, digest = LEAF
    record = parent.indices.span_record(start, end, entries, rows, rom)
    body = rom[start-parent.match.ROM_BASE:end-parent.match.ROM_BASE]
    if record['instrs'] != count or sha(body) != digest or start < address+len(data) and end > address:
        raise ValueError('leaf-only callee complete body identity/count differs')
    sites = {site: target for site, target in calls.items() if target == start}
    leaf = parent.FormalStackCalleeProof(body, start, rom, mapping, index, sites)
    restored = parent.frame.prove_frame(instructions, edges, address, {}, calls,
        stack_aliases=True, local_alias_slot_policy=parent.slots.SELECTOR,
        zero_index_profile=parent.zero_index.SELECTOR, formal_stack_callee_proof=leaf,
        formal_stack_alias_constant_policy=parent.slots.FORMAL_MOVS10_POLICY)
    additions = [row for row in restored['local_alias_slots']['small_SP_additions'] if row[2] == 10]
    if not additions:
        raise ValueError('leaf-only MOVS10 inventory requires an actual proved MOVS10 to SP constructor')
    modules = (parent, parent.analyze, parent.match, parent.thunks, parent.owner,
        parent.graph, parent.operations, parent.indices, parent.frame, parent.slots,
        parent.zero_index, parent.incoming)
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'address': address, 'end': address+len(data), 'instructions': len(instructions),
        'body_sha256': sha(data), 'ROM_sha256': sha(rom), 'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
        'calls': [[site, target, bindings[site]] for site, target in sorted(calls.items())],
        'frame': restored, 'partition': partition,
        'exact_MOVS10_SP_constructors': additions,
        'component_accounting': {'fresh_formal_leaf_workflows': 1, 'fresh_leaf_frames': 1,
            'fresh_caller_frames': 1, 'noop_workflows': 0},
        'ordinary_call_premise': 'conditional: every other ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI; its body and memory effects are not proved',
        'output_call_premise': 'entry-SP words0/4 carry proved live local pointers; actual arg3/formals4/5 halfword writes are discharged into caller abstract locals',
        'constant_domain': 'exact encoded MOVS1/2/3/10 only; all-path intersection; calls kill facts; no arithmetic-derived or unknown index',
        'complete_native_structural_proof': True, 'source_or_ELF_admission': False,
        'numeric_input_preconditions': [], 'numeric_return_facts': [], 'arithmetic_C_equivalence': False,
        'physical_memory_claim': False, 'memory_safety_claim': False, 'nonescape_claim': False,
        'universal_termination_claim': False,
        'claim': 'complete CFG/partition and reached-return abstract ABI restoration with fresh formal output effects and exact MOVS10 local constructor; other calls remain conditional',
        'producer_source_sha256': source_pins}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('leaf-only inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    selected = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(selected) != 1:
        raise ValueError('leaf-only inventory requires one exact caller row')
    data = rom[args.address-parent.match.ROM_BASE:int(selected[0]['end'], 16)-parent.match.ROM_BASE]
    _, _, calls, _ = parent.complete(data, args.address, rom, mapping, index)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    result, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(result))


if __name__ == '__main__':
    main()
