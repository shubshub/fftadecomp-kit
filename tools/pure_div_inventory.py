"""Explicit saved-only pure canonical signed-DIV structural inventory."""
import argparse
import hashlib
import json
from pathlib import Path

from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP

import divsi3_profile as quotient
import div_only_ordinary_inventory as existing

SELECTOR = 'pure-div-saved-only-structural-inventory-v1'
SCHEMA = 'thumb-pure-div-saved-only-structural-inventory-v1'
ZERO = existing.ZERO


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(value):
    return hashlib.sha256(value).hexdigest()


def bind_calls(calls, mapping, address, size, rom_size):
    import match
    if type(mapping) is not bytes or type(address) is not int or address % 2 or \
            type(size) is not int or size <= 0 or size % 2 or type(rom_size) is not int or \
            not match.ROM_BASE <= address < address + size <= match.ROM_BASE + rom_size or \
            type(calls) is not dict or not calls or any(
                type(site) is not int or type(target) is not int or site % 2 or
                not address <= site <= address + size - 4 or target != quotient.ADDRESS
                for site, target in calls.items()):
        raise ValueError('pure DIV inventory requires exact actual canonical DIV calls only')
    return {site: '__divsi3' for site in sorted(calls)}


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    import software_double_profile as canonical
    import software_float_profile as native
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('pure DIV inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or \
            type(address) is not int or type(calls) is not dict or type(bindings) is not dict:
        raise ValueError('pure DIV inventory requires immutable exact bytes and typed call records')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('pure DIV inventory requires its exact complete direct-call CFG and bindings')
    entries, rows = canonical.indices(mapping, index)
    if canonical.span_record(address, address + len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('pure DIV inventory requires exact dual-index reachable instruction counts')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    for instruction in instructions.values():
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('pure DIV inventory excludes non-ARMv4T widths')
        if match.uses_stack_frame((instruction,)) or instruction.mnemonic.startswith(('ldm', 'stm')) or any(
                operand.type == ARM_OP_MEM and
                (operand.mem.base == ARM_REG_SP or operand.mem.index == ARM_REG_SP) or
                instruction.mnemonic not in ('push', 'pop') and
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in instruction.operands):
            raise ValueError('pure DIV saved-only inventory excludes allocation, SP accesses/exports and block transfers')
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or match.function_thunk.reserved(value) or \
                match.is_udivsi3_address(value) or any(module.reserved(value) for module in
                (quotient, match.modsi3, match.umodsi3, match.ashldi3, canonical, native)):
            raise ValueError('pure DIV inventory cannot materialize runtime or thunk addresses')
    closure = canonical.prove_division_closure(rom, mapping, index)
    if set(closure) != {quotient.ADDRESS, ZERO} or \
            closure[quotient.ADDRESS]['returns'] != [0x0814273E, 0x08142748] or \
            closure[ZERO]['returns'] != [ZERO] or any(
                proof['writes'] or proof['stack_reads'] for proof in closure.values()):
        raise ValueError('pure DIV inventory requires complete exact DIV/zero native closures')
    runtime_frames = existing.runtime_frames(rom, mapping, closure)
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True)
    modules = (match, owner, graph, operations, frame, canonical, native, quotient, existing)
    sources = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    sources[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False,
        'claim': 'structural target-state ABI/effects at reached returns under complete canonical DIV/zero closure',
        'runtime_entry_domain': 'arbitrary32-bit entry-register patterns; no numeric preconditions',
        'runtime_input_semantics': 'unchanged native interpreter symbolic entry-register origins including actual zero-hook path',
        'arithmetic_C_equivalence': False, 'memory_safety_claim': False,
        'physical_stack_nonalias_claim': False, 'physical_memory_preservation_claim': False,
        'runtime_numeric_return_facts': [], 'numeric_operand_preconditions': [], 'nonzero_facts': [],
        'termination_claim': False,
        'control_flow_guarantee': 'every reached CFG region has a path to a checked return; universal termination is not proved',
        'dependencies': [list(row) for row in canonical.DIVISION_IDENTITIES],
        'native_runtime_closure': [[site, proof] for site, proof in sorted(closure.items())],
        'native_runtime_frames': runtime_frames,
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'ordinary_calls': [], 'indirect_calls': [], 'ordinary_call_premise': None,
        'caller_facts': 'every call clears caller-saved provenance; no numeric/address/flags result facts supplied',
        'caller_frame_policy': 'strict saved slots, SP, r4-r11 and entry-LR restoration; no local allocation, explicit SP access/export, entry-word or buffer permission',
        'runtime_stack_policy': 'canonical DIV/zero accesses only its independently proved own frames below caller SP in the existing abstract stack model',
        'frame': restored, 'partition': partition, 'instructions': len(instructions),
        'body_sha256': sha(data), 'ROM_sha256': sha(rom), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'producer_source_sha256': sources,
        'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('pure DIV inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    selected = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(selected) != 1:
        raise ValueError('pure DIV inventory requires one exact mapped owner')
    data = rom[args.address-0x08000000:int(selected[0]['end'], 16)-0x08000000]
    _, _, _, calls, _ = graph.graph(data, args.address, owner.refine(data, args.address, mapping))
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
