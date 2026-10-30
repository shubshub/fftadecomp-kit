"""Explicit single named-read output leaf inventory with live caller locals."""
import argparse
import json
from pathlib import Path

import ordinary_two_output_callees_inventory as named

parent = named.parent
LEAF = named.SECOND
SELECTOR = 'ordinary-named-output-leaf-only-inventory-v1'
SCHEMA = 'thumb-ordinary-named-output-leaf-only-inventory-v1'
sha, text = named.sha, named.text


def bind_calls(calls, mapping, address, size, rom_size):
    if type(calls) is not dict or not calls or type(mapping) is not bytes or \
            any(type(value) is not int for value in (address, size, rom_size)) or address % 2 or size <= 0 or \
            not parent.match.ROM_BASE <= address < address+size <= parent.match.ROM_BASE+rom_size:
        raise ValueError('named leaf-only inventory requires exact immutable ordinary call inputs')
    entries = json.loads(mapping)
    bound = {}
    for site, target in sorted(calls.items()):
        if type(site) is not int or type(target) is not int or site % 2 or \
                not address <= site <= address+size-4 or parent.thunks.reserved(target):
            raise ValueError('named leaf-only inventory excludes thunks and malformed calls')
        name = f'func_{target:08X}'
        actual = parent.match.function_address_target(name, entries, address, size, rom_size)
        rows = [row for row in entries if int(row['rom'], 16) == actual]
        end = int(rows[0]['end'], 16)
        if not actual < end <= parent.match.ROM_BASE+rom_size or actual < address+size and end > address or any(
                row is not rows[0] and int(row['rom'], 16) < end and int(row['end'], 16) > actual for row in entries):
            raise ValueError('named leaf-only target requires unique nonoverlapping complete ownership')
        bound[site] = name
    if list(calls.values()).count(LEAF[0]) != 1:
        raise ValueError('named leaf-only inventory requires exactly one actual named output call')
    return bound


def verify(data, address, rom, mapping, index, data_mapping, calls, bindings, *, selector,
           readonly_named_buffer_policy=None, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('named leaf-only inventory requires its explicit default-off selector')
    named.validate_named_policy(readonly_named_buffer_policy, data_mapping)
    instructions, edges, actual_calls, partition = parent.complete(data, address, rom, mapping, index)
    if type(calls) is not dict or calls != actual_calls or type(bindings) is not dict or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('named leaf-only bindings differ from every actual reached call')
    entries, rows = parent.indices.indices(mapping, index)
    start, end, count, digest = LEAF
    record = parent.indices.span_record(start, end, entries, rows, rom)
    body = rom[start-parent.match.ROM_BASE:end-parent.match.ROM_BASE]
    if record['instrs'] != count or sha(body) != digest or start < address+len(data) and end > address:
        raise ValueError('named leaf-only complete helper body identity/count differs')
    sites = {site: target for site, target in calls.items() if target == start}
    proof = named.NamedReadonlyFormalLeafProof(body, start, rom, mapping, index, data_mapping,
        sites, readonly_named_buffer_policy)
    restored = parent.frame.prove_frame(instructions, edges, address, {}, calls,
        stack_aliases=True, local_alias_slot_policy=parent.slots.SELECTOR,
        formal_stack_callee_proof=proof)
    modules = (named, parent, parent.analyze, parent.match, parent.thunks, parent.owner,
        parent.graph, parent.operations, parent.indices, parent.frame, parent.slots, parent.incoming)
    source = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'address': address, 'end': address+len(data), 'instructions': len(instructions),
        'body_sha256': sha(data), 'ROM_sha256': sha(rom), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'data_mapping_sha256': sha(data_mapping),
        'calls': [[site, target, bindings[site]] for site, target in sorted(calls.items())],
        'frame': restored, 'partition': partition,
        'readonly_named_buffer_policy': json.loads(text(readonly_named_buffer_policy)),
        'named_read_premise': named.READ_PREMISE,
        'component_accounting': {'fresh_named_helper_workflows': 1, 'fresh_helper_frames': 1,
            'fresh_caller_frames': 1, 'helper_store_events': 5, 'unique_write_footprints': 3},
        'ordinary_call_premise': 'conditional: every other ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI; its body and memory effects are not proved',
        'output_call_premise': 'the actual arg3 and initialized outgoing words0/4 contain live caller-local pointers; every freshly observed halfword write is discharged into allocated locals outside saved slots and outgoing words',
        'named_loaded_values': 'unknown scalars; no numeric or return facts',
        'complete_native_structural_proof': True, 'complete_argument_effect_proof': True,
        'source_or_ELF_admission': False, 'arithmetic_C_equivalence': False,
        'numeric_input_preconditions': [], 'numeric_return_facts': [],
        'physical_memory_claim': False, 'memory_safety_claim': False, 'nonescape_claim': False,
        'universal_termination_claim': False, 'producer_source_sha256': source,
        'claim': 'complete CFG/partition and reached-return abstract ABI restoration with one freshly proved named-read output leaf, an explicit typed named-read premise and conditional other ordinary ABI'}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('named leaf-only manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index', 'data-mapping'):
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('--readonly-named-buffer-policy', required=True, type=json.loads)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index, data_mapping = (args.rom.read_bytes(), args.mapping.read_bytes(),
        args.index.read_bytes(), args.data_mapping.read_bytes())
    selected = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(selected) != 1:
        raise ValueError('named leaf-only inventory requires one exact caller row')
    data = rom[args.address-parent.match.ROM_BASE:int(selected[0]['end'], 16)-parent.match.ROM_BASE]
    _, _, calls, _ = parent.complete(data, args.address, rom, mapping, index)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    result, _ = verify(data, args.address, rom, mapping, index, data_mapping, calls, bindings,
        selector=args.profile, readonly_named_buffer_policy=args.readonly_named_buffer_policy)
    print(text(result))


if __name__ == '__main__':
    main()
