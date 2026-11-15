"""Explicit canonical integer closure with bounded constant-offset private locals."""
import hashlib
import json
from pathlib import Path
import canonical_integer_scalar_inventory as core

SELECTOR = 'canonical-integer-private-locals-inventory-v1'
SCHEMA = 'thumb-canonical-integer-private-locals-inventory-v1'
OPERATIONS, SPECS, ZERO = core.OPERATIONS, core.SPECS, core.ZERO
canonical, division, quotient = core.canonical, core.division, core.quotient
unsigned_frames, unsigned_remainder = core.unsigned_frames, core.unsigned_remainder
bind_calls, prove_called_closures = core.bind_calls, core.prove_called_closures
text, sha = core.text, core.sha

def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    import function_thunk_profile as thunks
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('canonical integer private locals inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or \
            type(address) is not int or type(calls) is not dict or type(bindings) is not dict:
        raise ValueError('canonical integer private locals inventory requires immutable exact bytes and typed call records')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('canonical integer private locals inventory requires exact complete direct-call CFG and bindings')
    entries, rows = canonical.indices(mapping, index)
    if canonical.span_record(address, address + len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('canonical integer caller dual-index count differs from complete CFG')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    adjustments = []
    for instruction in instructions.values():
        adjustment = match.thumb_stack_adjustment(instruction)
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('canonical integer private locals inventory excludes non-ARMv4T widths')
        if instruction.mnemonic.startswith(('ldm', 'stm')):
            raise ValueError('canonical integer private locals exclude block transfers')
        if adjustment is not None:
            adjustments.append([instruction.address, adjustment])
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or thunks.reserved(value) or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (match.divsi3, match.modsi3, match.umodsi3,
                    match.ashldi3, match.software_double, match.software_float)):
            raise ValueError('canonical integer private locals inventory cannot materialize runtime or thunk addresses')
    # Existing constant-offset aliases only; no entry words, output buffers or spills.
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True)
    if not restored['local_aliases']['accesses']:
        raise ValueError('canonical integer private locals require actual bounded local alias accesses')
    if restored['maximum_frame_bytes'] <= 0:
        raise ValueError('canonical integer private locals inventory requires an allocated-or-saved caller frame')
    families = set(bindings.values()) & OPERATIONS.keys()
    closure, native_frames, components = prove_called_closures(rom, mapping, index, families)
    modules = (match, match.armv4t, thunks, owner, graph, operations, frame, canonical, division,
               quotient, unsigned_frames, unsigned_remainder, match.software_float)
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
        'caller_frame_policy': 'existing bounded constant-offset byte/halfword/word local aliases; no call argument escape, spill, incoming words, buffer permission or initialized-content theorem; r4-r11/SP/entry-LR restoration',
        'runtime_stack_policy': 'each canonical runtime accesses only its independently proved abstract frame below current caller SP; no caller writes or stack reads',
        'external_memory_effect_boundary': 'ordinary non-SP scalar memory operations retain existing structural policy; physical addresses, nonalias and memory safety are not proved',
        'stack_adjustments_in_words': adjustments, 'backward_edges': [[site, target]
            for site, targets in sorted(edges.items()) for target in targets if target <= site],
        'frame': restored, 'partition': partition, 'instructions': len(instructions),
        'address': address, 'end': address+len(data), 'body_sha256': sha(data),
        'mapping_sha256': sha(mapping), 'index_sha256': sha(index), 'ROM_sha256': sha(rom),
        'producer_source_sha256': source_pins}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('canonical integer private locals inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]

