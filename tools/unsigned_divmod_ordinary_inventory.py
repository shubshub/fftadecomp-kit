"""Explicit saved-only structural inventory of canonical unsigned DIV and MOD."""
import argparse
import hashlib
import json
from pathlib import Path

import zero_aware_unsigned_quotient_inventory as quotient
import umod_only_ordinary_inventory as remainder

SELECTOR = 'unsigned-divmod-ordinary-structural-inventory-v1'
SCHEMA = 'thumb-unsigned-divmod-ordinary-structural-inventory-v1'
ZERO = remainder.ZERO
OPERATIONS = {'__udivsi3': quotient.UDIV, '__umodsi3': remainder.remainder.ADDRESS}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def bind_calls(calls, mapping, address, size, rom_size):
    import match
    import function_thunk_profile as thunks
    if type(mapping) is not bytes or type(address) is not int or address % 2 or \
            type(size) is not int or size <= 0 or type(rom_size) is not int or \
            not match.ROM_BASE <= address < address+size <= match.ROM_BASE+rom_size or \
            type(calls) is not dict or not set(OPERATIONS.values()) <= set(calls.values()) or any(
                type(site) is not int or type(target) is not int or site % 2 or
                not address <= site <= address+size-4 for site, target in calls.items()):
        raise ValueError('unsigned DIV/MOD requires both exact canonical runtime call families')
    entries = json.loads(mapping)
    names = {target: name for name, target in OPERATIONS.items()}
    bindings = {}
    for site, target in sorted(calls.items()):
        if target in names:
            bindings[site] = names[target]
            continue
        if thunks.reserved(target):
            raise ValueError('unsigned DIV/MOD excludes reserved indirect-call thunks')
        name = f'func_{target:08X}'
        actual = match.function_address_target(name, entries, address, size, rom_size)
        row = next(row for row in entries if int(row['rom'], 16) == actual)
        end = int(row['end'], 16)
        if not actual < end <= match.ROM_BASE+rom_size or \
                actual < address+size and end > address or any(
                    other is not row and int(other['rom'], 16) < end and
                    int(other['end'], 16) > actual for other in entries):
            raise ValueError('ordinary call requires one unique nonoverlapping mapped Thumb span')
        bindings[site] = name
    return bindings


def runtime_closure(rom, mapping, index):
    """Compose existing native proofs; independently check the UDIV saved frame."""
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    from capstone.arm import ARM_OP_MEM, ARM_REG_SP, ARM_REG_R4, ARM_REG_R11
    qproofs = quotient.prove_quotient_closure(rom, mapping, index)
    rproofs, rframes = remainder.runtime_closure(rom, mapping, index)
    proofs, frames = dict(rproofs), dict(rframes)
    if set(qproofs) != {ZERO, quotient.UDIV} or set(proofs) != {ZERO, OPERATIONS['__umodsi3']} or \
            qproofs[ZERO] != proofs[ZERO] or any(
                proof['writes'] or proof['stack_reads'] for proof in qproofs.values()) or \
            qproofs[quotient.UDIV]['returns'] != [0x08142B1C, 0x08142B26]:
        raise ValueError('unsigned DIV/MOD requires equal real zero closures and every native return')
    address, end = quotient.UDIV, 0x08142B28
    data = rom[address-match.ROM_BASE:end-match.ROM_BASE]
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != {0x08142B20: ZERO} or any(
            operand.mem.base != ARM_REG_SP or operand.mem.index for instruction in instructions.values()
            for operand in instruction.operands if operand.type == ARM_OP_MEM):
        raise ValueError('unsigned quotient frame requires its exact zero call and stack-only accesses')
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11+1))
    restored = frame.prove_frame(instructions, edges, address, {}, calls,
        call_preservation={site: preserved for site in calls})
    if restored['returns'] != qproofs[address]['returns']:
        raise ValueError('unsigned quotient independent frame return coverage differs')
    frames[address] = {'frame': restored, 'maximum_additional_stack_bytes':
        restored['maximum_frame_bytes']+frames[ZERO]['maximum_additional_stack_bytes'],
        'caller_memory_writes': [], 'caller_stack_reads': [], 'restores': 'r4-r11,sp,entry-lr'}
    proofs.update(qproofs)
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
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP, ARM_REG_R4, ARM_REG_R11
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('unsigned DIV/MOD requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('unsigned DIV/MOD requires immutable exact ROM and dual-index bytes')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or type(calls) is not dict or calls != actual_calls or \
            type(bindings) is not dict or bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('unsigned DIV/MOD requires exact complete direct-call CFG and bindings')
    entries, rows = complete.indices(mapping, index)
    if complete.span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('unsigned DIV/MOD caller dual-index count differs from native CFG')
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
        raise ValueError('unsigned DIV/MOD excludes local CFG cycles')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    for instruction in instructions.values():
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('unsigned DIV/MOD excludes non-ARMv4T instruction widths')
        if instruction.mnemonic.startswith(('ldm', 'stm')) or any(
                operand.type == ARM_OP_MEM and (operand.mem.base == ARM_REG_SP or operand.mem.index == ARM_REG_SP) or
                instruction.mnemonic not in ('push', 'pop') and operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in instruction.operands):
            raise ValueError('unsigned DIV/MOD saved-only frame excludes locals, entry words and SP exports')
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or thunks.reserved(value) or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (remainder.remainder, match.divsi3, match.modsi3,
                    match.ashldi3, match.software_double, match.software_float)):
            raise ValueError('unsigned DIV/MOD cannot materialize reserved runtime or thunk addresses')
    closure, runtime_frames = runtime_closure(rom, mapping, index)
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11+1))
    ordinary = [[site-address, name] for site, name in sorted(bindings.items()) if name not in OPERATIONS]
    restored = frame.prove_frame(instructions, edges, address, {}, calls,
        **({} if ordinary else {'call_preservation': {site: preserved for site in calls}}))
    modules = (match, thunks, owner, graph, operations, frame, complete, quotient, remainder,
        remainder.remainder, match.software_double, match.software_float)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True, 'source_or_ELF_admission': False,
        'claim': 'acyclic local structural CFG/frame and restoration at every reached return',
        'arithmetic_C_equivalence': False, 'memory_safety_claim': False, 'termination_claim': False,
        'physical_memory_nonalias_claim': False, 'runtime_numeric_return_facts': [],
        'runtime_entry_domain': 'unchanged native interpreter arbitrary32-bit scalar entry origins, including real zero paths',
        'numeric_input_preconditions': [], 'entry_stack_contract': None, 'cycles_present': False,
        'ordinary_calls': ordinary, 'ordinary_call_premise': (
            'conditional: each ordinary callee returns and obeys existing r4-r11/SP/entry-LR preserving direct-call ABI; no native callee or memory-effects proof'
            if ordinary else None),
        'caller_frame_policy': 'saved-only strict frame; no allocated locals, entry words, stack aliases or SP exports',
        'caller_facts': 'calls kill caller-saved provenance; no numeric return, address or flags facts',
        'runtime_stack_policy': 'canonical UDIV/UMOD/zero access only independently proved frames below caller SP',
        'native_runtime_closure': closure, 'native_runtime_frames': runtime_frames, 'shared_zero_identity_equal': True,
        'dependencies': {'quotient': [list(row) for row in match.UDIVSI3_IDENTITIES],
            'remainder': [list(row) for row in remainder.remainder.IDENTITIES]},
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'frame': restored, 'partition': partition, 'instructions': len(instructions), 'address': address,
        'end': address+len(data), 'body_sha256': sha(data), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'ROM_sha256': sha(rom), 'producer_source_sha256': pins,
        'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('unsigned DIV/MOD manifest differs from fresh native proof')
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
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('unsigned DIV/MOD requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(rows[0]['end'], 16)-match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
