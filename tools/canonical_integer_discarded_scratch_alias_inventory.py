"""Explicit structural canonical integer inventory with bounded local aliases and an explicit discarded-scratch return ABI."""
import argparse
import json
from pathlib import Path

import canonical_integer_scalar_inventory as core
import zero_index_stack_profile as zero_index

SELECTOR = 'canonical-integer-discarded-scratch-alias-inventory-v1'
SCHEMA = 'thumb-canonical-integer-discarded-scratch-alias-inventory-v1'
ZERO, OPERATIONS, SPECS = core.ZERO, core.OPERATIONS, core.SPECS
sha, text = core.sha, core.text
bind_calls = core.bind_calls
prove_called_closures = core.prove_called_closures
canonical = core.canonical
POLICY = {'schema': 'thumb-discarded-exit-scratch-v1', 'registers': [2, 3]}


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, discarded_exit_scratch, manifest=None):
    import match
    import function_thunk_profile as thunks
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('canonical integer discarded scratch alias inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or \
            type(address) is not int or type(calls) is not dict or type(bindings) is not dict:
        raise ValueError('canonical integer discarded scratch alias inventory requires immutable exact bytes and typed call records')
    frame.validate_discarded_exit_scratch(discarded_exit_scratch)
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('canonical integer discarded scratch alias inventory requires exact complete direct-call CFG and bindings')
    entries, rows = canonical.indices(mapping, index)
    if canonical.span_record(address, address + len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('canonical integer caller dual-index count differs from complete CFG')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    adjustments = []
    for instruction in instructions.values():
        adjustment = match.thumb_stack_adjustment(instruction)
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('canonical integer discarded scratch alias inventory excludes non-ARMv4T widths')
        if instruction.mnemonic.startswith(('ldm', 'stm')):
            raise ValueError('canonical integer discarded scratch alias inventory excludes block transfers')
        if adjustment is not None:
            adjustments.append([instruction.address, adjustment])
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or thunks.reserved(value) or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (match.divsi3, match.modsi3, match.umodsi3,
                    match.ashldi3, match.software_double, match.software_float)):
            raise ValueError('canonical integer discarded scratch alias inventory cannot materialize runtime or thunk addresses')
    # Existing local-only alias fixpoint, with no entry, buffer, spill or argument-escape permission.
    restored = frame.prove_frame(instructions, edges, address, {}, calls,
        stack_aliases=True, zero_index_profile=zero_index.SELECTOR,
        discarded_exit_scratch=discarded_exit_scratch)
    if restored['maximum_frame_bytes'] <= 0 or not restored['local_aliases']['assignments'] or not restored['local_aliases']['accesses']:
        raise ValueError('canonical integer discarded scratch alias inventory requires actual bounded allocated local alias accesses')
    if not restored['discarded_exit_scratch']['residual_aliases']:
        raise ValueError('discarded scratch inventory requires actual residual local alias provenance')
    families = set(bindings.values()) & OPERATIONS.keys()
    closure, native_frames, components = prove_called_closures(rom, mapping, index, families)
    modules = (match, thunks, owner, graph, operations, frame, core, zero_index, canonical, core.division,
               core.quotient, core.unsigned_frames, core.unsigned_remainder, match.software_float)
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    ends = {target: SPECS[name][0] for name, target in OPERATIONS.items()} | {ZERO: ZERO+2}
    ordinary = [[site-address, name] for site, name in sorted(bindings.items()) if name not in OPERATIONS]
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False, 'complete_native_structural_proof': True,
        'claim': 'structural target-state ABI/effects at reached returns and a checked return path from every reached CFG region',
        'runtime_entry_domain': 'unchanged native interpreter arbitrary32-bit scalar entry origins, including real zero-hook paths',
        'numeric_operand_preconditions': [], 'numeric_input_preconditions': [],
        'runtime_numeric_return_facts': [], 'nonzero_facts': [],
        'arithmetic_C_equivalence': False, 'termination_claim': False, 'memory_safety_claim': False,
        'physical_caller_stack_nonalias_proof': False, 'physical_frame_preservation_claim': False,
        'control_flow_guarantee': 'complete cycles and every reached region has a checked return path; no universal termination claim',
        'runtime_families': sorted(families), 'runtime_component_accounting': components,
        'shared_zero_native_and_frame_agreement': True,
        'native_runtime_closure': [[site, proof] for site, proof in sorted(closure.items())],
        'native_runtime_frames': [[site, proof] for site, proof in sorted(native_frames.items())],
        'dependencies': [[site, ends[site], sha(rom[site-match.ROM_BASE:ends[site]-match.ROM_BASE])]
                         for site in sorted(closure)],
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name in OPERATIONS],
        'ordinary_calls': ordinary,
        'ordinary_call_premise': ('conditional: every ordinary callee returns and obeys existing r4-r11/SP preserving direct-call ABI; no native ordinary-callee or memory-effects proof' if ordinary else None),
        'ordinary_call_stack_bound': None, 'entry_stack_contract': None,
        'caller_facts': 'calls clear caller-saved provenance; no numeric result, address or flags facts granted',
        'caller_frame_policy': 'existing strict local-only constant-offset alias frame; aligned byte/halfword/word local accesses, exact proven-zero signed register-index loads; no incoming words, alias spills, buffer or pointer-call/return permission',
        'zero_index_profile': zero_index.SELECTOR, 'entry_ABI_preconditions': [],
        'discarded_exit_scratch_policy': discarded_exit_scratch,
        'discarded_scratch_ABI_premise': frame.DISCARDED_SCRATCH_CONTRACT,
        'native_nonescape_proof': False,
        'local_alias_policy': 'dereferences stay within live allocated locals; native fixpoint checks joins, lifetimes, call arguments, saved slots and all restored returns; residual r2/r3 addresses require the explicit discarded-scratch ABI premise',
        'runtime_stack_policy': 'each canonical runtime accesses only its independently proved abstract frame below current caller SP; no caller writes or stack reads',
        'external_memory_effect_boundary': 'ordinary non-SP scalar memory operations retain existing structural policy; physical addresses, nonalias and memory safety are not proved',
        'stack_adjustments_in_words': adjustments, 'backward_edges': [[site, target]
            for site, targets in sorted(edges.items()) for target in targets if target <= site],
        'frame': restored, 'partition': partition, 'instructions': len(instructions),
        'address': address, 'end': address+len(data), 'body_sha256': sha(data),
        'mapping_sha256': sha(mapping), 'index_sha256': sha(index), 'ROM_sha256': sha(rom),
        'producer_source_sha256': source_pins}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('canonical integer discarded scratch alias inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    parser.add_argument('--discarded-exit-scratch', required=True, choices=('r2,r3',))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    selected = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(selected) != 1:
        raise ValueError('canonical integer discarded scratch alias inventory requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(selected[0]['end'], 16)-match.ROM_BASE]
    _, _, _, calls, _ = graph.graph(data, args.address, owner.refine(data, args.address, mapping))
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile,
        discarded_exit_scratch=POLICY)
    print(text(observed))


if __name__ == '__main__':
    main()
