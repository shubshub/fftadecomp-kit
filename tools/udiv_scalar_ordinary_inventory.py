"""Opt-in UDIV structural inventory with allocated scalar frames and ordinary calls."""
import argparse
import hashlib
import json
from pathlib import Path

import zero_aware_unsigned_quotient_inventory as quotient
import udiv_constant_choices_inventory as shared

SELECTOR = 'udiv-scalar-ordinary-inventory-v1'
SCHEMA = 'thumb-udiv-scalar-ordinary-inventory-v1'
ZERO = 0x0814274C


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(data):
    return hashlib.sha256(data).hexdigest()


# These structural factories carry no finite-divisor choice precondition.
# The existing finite-choice profile itself remains unchanged and default-off.
bind_calls = shared.bind_calls
runtime_frames = shared.runtime_frames


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    import function_thunk_profile as thunks
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    import unsigned_remainder_closure_inventory as complete
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('UDIV scalar inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('UDIV scalar inventory requires immutable exact ROM and index bytes')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or type(calls) is not dict or calls != actual_calls or \
            type(bindings) is not dict or bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('UDIV scalar inventory requires exact complete direct-call CFG and bindings')
    entries, rows = complete.indices(mapping, index)
    if complete.span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('UDIV scalar caller dual-index count differs from its complete CFG')
    degree = {site: 0 for site in instructions}
    for targets in edges.values():
        for target in targets:
            degree[target] += 1
    pending, visited = [site for site in instructions if not degree[site]], 0
    while pending:
        site = pending.pop()
        visited += 1
        for target in edges[site]:
            degree[target] -= 1
            if not degree[target]:
                pending.append(target)
    if visited != len(instructions):
        raise ValueError('UDIV scalar inventory excludes local CFG cycles')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    adjustments = []
    for instruction in instructions.values():
        adjustment = match.thumb_stack_adjustment(instruction)
        if instruction.mnemonic.startswith(('ldm', 'stm')) or any(
                operand.type == ARM_OP_MEM and operand.mem.index == ARM_REG_SP or
                instruction.mnemonic not in ('push', 'pop') and adjustment is None and
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP for operand in instruction.operands):
            raise ValueError('UDIV scalar frame excludes stack-address materialization and block transfers')
        if adjustment is not None:
            adjustments.append([instruction.address, adjustment])
    if not any(delta < 0 for _, delta in adjustments):
        raise ValueError('UDIV scalar inventory requires actual allocated scalar locals')
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or thunks.reserved(value) or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (match.umodsi3, match.divsi3, match.modsi3,
                    match.ashldi3, match.software_double, match.software_float)):
            raise ValueError('UDIV scalar inventory cannot materialize runtime or thunk addresses')
    restored = frame.prove_frame(instructions, edges, address, {}, calls)
    closure = quotient.prove_quotient_closure(rom, mapping, index)
    if set(closure) != {quotient.UDIV, ZERO} or \
            closure[quotient.UDIV]['returns'] != [0x08142B1C, 0x08142B26] or \
            closure[ZERO]['returns'] != [ZERO] or any(
                proof['writes'] or proof['stack_reads'] for proof in closure.values()):
        raise ValueError('UDIV scalar inventory requires complete exact UDIV/zero native closures')
    native_frames = runtime_frames(rom, mapping, closure)
    modules = (match, thunks, owner, graph, operations, frame, quotient, shared, complete,
        match.software_double, match.software_float)
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True, 'source_or_ELF_admission': False,
        'claim': 'acyclic local structural CFG/frame/reached-return inventory under exact UDIV/zero closure and conditional ordinary returning-call ABI',
        'arithmetic_C_equivalence': False, 'memory_safety_claim': False, 'termination_claim': False,
        'control_flow_guarantee': 'every reached region has a checked return path; no universal termination claim',
        'runtime_entry_domain': 'unchanged native interpreter arbitrary32-bit scalar entry origins, including exact zero-hook path',
        'numeric_input_preconditions': [], 'dividend_requirement': None, 'runtime_numeric_return_facts': [],
        'divisor_policy': 'no divisor restriction or numeric result fact; unchanged arbitrary32 scalar runtime entry',
        'numeric_operand_preconditions': [], 'nonzero_facts': [],
        'native_runtime_closure': [[site, proof] for site, proof in sorted(closure.items())],
        'native_runtime_frames': native_frames,
        'dependencies': [[quotient.UDIV, 0x08142B28, sha(rom[quotient.UDIV-match.ROM_BASE:0x08142B28-match.ROM_BASE])],
                         [ZERO, ZERO+2, sha(rom[ZERO-match.ROM_BASE:ZERO+2-match.ROM_BASE])]],
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name == '__udivsi3'],
        'ordinary_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name != '__udivsi3'],
        'ordinary_call_premise': 'conditional: every ordinary callee returns and obeys existing r4-r11/SP preserving direct-call ABI; no native ordinary-callee or memory-effects proof',
        'physical_caller_stack_nonalias_proof': False, 'physical_frame_preservation_claim': False,
        'ordinary_call_stack_bound': None,
        'caller_facts': 'calls clear caller-saved provenance; no numeric result, address or flags facts granted',
        'caller_frame_policy': 'strict scalar allocated locals, saved slots, r4-r11/SP/entry-LR restoration; no SP address, entry-word, local-alias or buffer permissions',
        'runtime_stack_policy': 'canonical UDIV/zero accesses only independently proved own frames below caller SP',
        'cycles_present': False, 'entry_stack_contract': None, 'stack_adjustments': adjustments,
        'frame': restored, 'partition': partition, 'instructions': len(instructions),
        'address': address, 'end': address+len(data), 'body_sha256': sha(data), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'ROM_sha256': sha(rom), 'producer_source_sha256': source_pins,
        'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('UDIV scalar inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
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
        raise ValueError('UDIV scalar inventory requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(selected[0]['end'], 16)-match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
