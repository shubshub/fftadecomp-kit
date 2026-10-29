"""Explicit UMOD-only constant-divisor inventory with scalar frames and ordinary calls."""
import argparse
import hashlib
import json
from pathlib import Path

import umodsi3_profile as remainder

SELECTOR = 'umod-only-ordinary-constant-inventory-v1'
SCHEMA = 'thumb-umod-only-ordinary-constant-inventory-v1'
ZERO = 0x0814274C


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def bind_calls(calls, mapping, address, size, rom_size):
    import match
    import function_thunk_profile as thunks
    if type(mapping) is not bytes or type(address) is not int or address % 2 or \
            type(size) is not int or size <= 0 or type(rom_size) is not int or \
            not match.ROM_BASE <= address < address+size <= match.ROM_BASE+rom_size or \
            type(calls) is not dict or not calls or any(type(site) is not int or
                type(target) is not int or site % 2 or not address <= site <= address+size-4
                for site, target in calls.items()):
        raise ValueError('UMOD-only inventory requires exact complete actual call sites')
    entries = json.loads(mapping)
    bindings = {}
    for site, target in sorted(calls.items()):
        if target == remainder.ADDRESS:
            bindings[site] = '__umodsi3'
            continue
        if thunks.reserved(target):
            raise ValueError('UMOD-only ordinary calls exclude reserved call thunks')
        name = f'func_{target:08X}'
        actual = match.function_address_target(name, entries, address, size, rom_size)
        row = next(row for row in entries if int(row['rom'], 16) == actual)
        end = int(row['end'], 16)
        if not actual < end <= match.ROM_BASE+rom_size or \
                actual < address+size and end > address or any(
                    other is not row and int(other['rom'], 16) < end and
                    int(other['end'], 16) > actual for other in entries):
            raise ValueError('ordinary call requires a unique nonoverlapping mapped target span')
        bindings[site] = name
    if '__umodsi3' not in bindings.values() or not any(name != '__umodsi3' for name in bindings.values()):
        raise ValueError('UMOD-only inventory requires actual UMOD and ordinary calls')
    return bindings


def runtime_closure(rom, mapping, index):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    import unsigned_remainder_closure_inventory as complete
    from capstone.arm import ARM_OP_MEM, ARM_REG_SP, ARM_REG_R4, ARM_REG_R11
    remainder.verify_identity(rom, mapping)
    entries, rows = complete.indices(mapping, index)
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11+1))
    proofs, frames = {}, {}
    for address, end, count, calls, returns in complete.SPECS:
        if address not in (ZERO, remainder.ADDRESS):
            continue
        span = complete.span_record(address, end, entries, rows, rom)
        if span['instrs'] != count:
            raise ValueError('UMOD-only runtime requires exact dual-index counts')
        proof = complete.prove_runtime(rom, entries, address, end, count, proofs,
            call_edges=calls, scalar_entries=(address,), allowed_writes=(), thumb_pc_returns=returns)
        if proof['returns'] != list(returns) or proof['writes'] or proof['stack_reads']:
            raise ValueError('UMOD-only runtime requires complete returns and no caller-memory effects')
        data = rom[address-match.ROM_BASE:end-match.ROM_BASE]
        refinement = owner.refine(data, address, mapping)
        instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
        if branches or words or any(target not in proofs for target in actual_calls.values()) or any(
                operand.mem.base != ARM_REG_SP or operand.mem.index for instruction in instructions.values()
                for operand in instruction.operands if operand.type == ARM_OP_MEM):
            raise ValueError('UMOD-only runtime requires exact proved calls and stack-only accesses')
        restored = frame.prove_frame(instructions, edges, address, {}, actual_calls,
            call_preservation={site: preserved for site in actual_calls})
        if restored['returns'] != list(returns):
            raise ValueError('UMOD-only runtime frame return coverage differs')
        frames[address] = {'frame': restored, 'maximum_additional_stack_bytes': restored['maximum_frame_bytes'] +
            max((frames[target]['maximum_additional_stack_bytes'] for target in actual_calls.values()), default=0),
            'caller_memory_writes': [], 'caller_stack_reads': [], 'restores': 'r4-r11,sp,entry-lr'}
        proofs[address] = proof
    if set(proofs) != {ZERO, remainder.ADDRESS}:
        raise ValueError('UMOD-only runtime closure must contain exactly canonical UMOD and zero hook')
    return ([[site, proof] for site, proof in sorted(proofs.items())],
            [[site, proof] for site, proof in sorted(frames.items())])


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
        raise ValueError('UMOD-only inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('UMOD-only inventory requires immutable exact ROM and index bytes')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or type(calls) is not dict or calls != actual_calls or \
            type(bindings) is not dict or bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('UMOD-only inventory requires exact complete direct-call CFG and bindings')
    entries, rows = complete.indices(mapping, index)
    if complete.span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('UMOD-only caller dual-index count differs from its complete CFG')
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
        raise ValueError('UMOD-only inventory excludes local CFG cycles')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    adjustments = []
    for instruction in instructions.values():
        adjustment = match.thumb_stack_adjustment(instruction)
        if instruction.mnemonic.startswith(('ldm', 'stm')) or any(
                operand.type == ARM_OP_MEM and operand.mem.index == ARM_REG_SP or
                instruction.mnemonic not in ('push', 'pop') and adjustment is None and
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP for operand in instruction.operands):
            raise ValueError('UMOD-only scalar frame excludes stack-address materialization and block transfers')
        if adjustment is not None:
            adjustments.append([instruction.address, adjustment])
    if not any(delta < 0 for _, delta in adjustments):
        raise ValueError('UMOD-only inventory requires actual allocated scalar locals')
    runtime_sites = {site: target for site, target in calls.items() if target == remainder.ADDRESS}
    divisors = remainder.prove_divisors(instructions, edges, address, runtime_sites)
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or thunks.reserved(value) or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (remainder, match.divsi3, match.modsi3,
                    match.ashldi3, match.software_double, match.software_float)):
            raise ValueError('UMOD-only inventory cannot materialize runtime or thunk addresses')
    closure, runtime_frames = runtime_closure(rom, mapping, index)
    restored = frame.prove_frame(instructions, edges, address, {}, calls)
    modules = (match, thunks, owner, graph, operations, frame, remainder, complete,
        match.software_double, match.software_float)
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True, 'source_or_ELF_admission': False,
        'claim': 'acyclic local structural CFG/frame/reached-return inventory under exact UMOD/zero closure and conditional ordinary returning-call ABI',
        'arithmetic_C_equivalence': False, 'memory_safety_claim': False, 'termination_claim': False,
        'control_flow_guarantee': 'every reached region has a checked return path; no universal termination claim',
        'runtime_entry_domain': 'unchanged native interpreter arbitrary32-bit scalar entry origins, including exact zero-hook path',
        'numeric_input_preconditions': [], 'dividend_requirement': None, 'runtime_numeric_return_facts': [],
        'caller_divisors': [[site-address, divisor] for site, divisor in sorted(divisors.items())],
        'divisor_policy': 'unchanged all-path nonzero unsigned32 constant proof; every actual UMOD site, calls kill caller-saved facts',
        'native_runtime_closure': closure, 'native_runtime_frames': runtime_frames,
        'dependencies': [list(row) for row in remainder.IDENTITIES],
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name == '__umodsi3'],
        'ordinary_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name != '__umodsi3'],
        'ordinary_call_premise': 'conditional: every ordinary callee returns and obeys existing r4-r11/SP preserving direct-call ABI; no native ordinary-callee or memory-effects proof',
        'caller_facts': 'calls clear caller-saved provenance; no numeric result, address or flags facts granted',
        'caller_frame_policy': 'strict scalar allocated locals, saved slots, r4-r11/SP/entry-LR restoration; no SP address, entry-word, local-alias or buffer permissions',
        'runtime_stack_policy': 'canonical UMOD/zero accesses only independently proved own frames below caller SP',
        'cycles_present': False, 'entry_stack_contract': None, 'stack_adjustments': adjustments,
        'frame': restored, 'partition': partition, 'instructions': len(instructions),
        'address': address, 'end': address+len(data), 'body_sha256': sha(data), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'ROM_sha256': sha(rom), 'producer_source_sha256': source_pins,
        'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('UMOD-only inventory manifest differs from fresh native proof')
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
        raise ValueError('UMOD-only inventory requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(selected[0]['end'], 16)-match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
