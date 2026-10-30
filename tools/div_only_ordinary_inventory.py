"""Explicit DIV-only structural inventory with conditional ordinary calls."""
import argparse
import hashlib
import json
from pathlib import Path

import divsi3_profile as quotient

SELECTOR = 'div-only-ordinary-target-state-inventory-v1'
SCHEMA = 'thumb-div-only-ordinary-target-state-inventory-v1'
ZERO = 0x0814274C


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(value):
    return hashlib.sha256(value).hexdigest()


def bind_calls(calls, mapping, address, size, rom_size):
    import match
    import function_thunk_profile as thunks
    if type(mapping) is not bytes or type(address) is not int or address % 2 or \
            type(size) is not int or size <= 0 or type(rom_size) is not int or \
            not match.ROM_BASE <= address < address+size <= match.ROM_BASE+rom_size or \
            type(calls) is not dict or not calls or any(
                type(site) is not int or type(target) is not int or site % 2 or
                not address <= site <= address+size-4 for site, target in calls.items()):
        raise ValueError('DIV-only inventory requires exact complete actual call sites')
    entries = json.loads(mapping)
    bindings = {}
    for site, target in sorted(calls.items()):
        if target == quotient.ADDRESS:
            bindings[site] = '__divsi3'
            continue
        if thunks.reserved(target):
            raise ValueError('DIV-only ordinary calls exclude reserved call thunks')
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
    if '__divsi3' not in bindings.values() or not any(name != '__divsi3' for name in bindings.values()):
        raise ValueError('DIV-only inventory requires actual DIV and ordinary calls')
    return bindings


def runtime_frames(rom, mapping, closure):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    from capstone.arm_const import ARM_REG_R4, ARM_REG_R11
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11+1))
    proven = {}
    for address, end in ((ZERO, ZERO+2), (quotient.ADDRESS, 0x0814274A)):
        data = rom[address-0x08000000:end-0x08000000]
        refinement = owner.refine(data, address, mapping)
        instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
        if branches or words or any(target not in proven for target in calls.values()) or \
                closure[address]['writes'] or closure[address]['stack_reads']:
            raise ValueError('DIV-only runtime requires exact dependencies and no caller-memory effects')
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
                                    call_preservation={site: preserved for site in calls})
        if restored['returns'] != closure[address]['returns']:
            raise ValueError('DIV-only runtime frame return coverage differs')
        proven[address] = {'frame': restored,
            'maximum_additional_stack_bytes': restored['maximum_frame_bytes'] + max(
                (proven[target]['maximum_additional_stack_bytes'] for target in calls.values()), default=0),
            'caller_memory_writes': [], 'caller_stack_reads': [],
            'restores': 'r4-r11,sp,entry-lr'}
    return [[address, proof] for address, proof in sorted(proven.items())]


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    import software_double_profile as canonical
    import software_float_profile as native
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('DIV-only inventory requires its explicit inventory-only selector')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('DIV-only inventory requires its exact complete direct-call CFG and bindings')
    entries, rows = canonical.indices(mapping, index)
    if canonical.span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('DIV-only inventory requires exact dual-index reachable instruction counts')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    if match.uses_stack_frame(instructions.values()):
        raise ValueError('DIV-only inventory requires a caller without allocated locals')
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or match.function_thunk.reserved(value) or \
                match.is_udivsi3_address(value) or any(module.reserved(value) for module in
                (quotient, match.modsi3, match.umodsi3, match.ashldi3, canonical, native)):
            raise ValueError('DIV-only inventory cannot materialize runtime or thunk addresses')
    closure = canonical.prove_division_closure(rom, mapping, index)
    if set(closure) != {quotient.ADDRESS, ZERO} or \
            closure[quotient.ADDRESS]['returns'] != [0x0814273E, 0x08142748] or \
            closure[ZERO]['returns'] != [ZERO] or any(
                proof['writes'] or proof['stack_reads'] for proof in closure.values()):
        raise ValueError('DIV-only inventory requires complete exact DIV/zero native closures')
    native_frames = runtime_frames(rom, mapping, closure)
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True)
    modules = (match, owner, graph, operations, frame, canonical, native, quotient)
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False,
        'claim': 'structural target-state ABI/effects at reached returns under exact DIV/zero closure and conditional ordinary returning-call ABI',
        'runtime_entry_domain': 'arbitrary32-bit entry-register patterns; no numeric preconditions',
        'arithmetic_C_equivalence': False, 'memory_safety_claim': False,
        'runtime_numeric_return_facts': [], 'numeric_operand_preconditions': [], 'nonzero_facts': [],
        'termination_claim': False,
        'control_flow_guarantee': 'every reached CFG region has a path to a checked return; universal termination is not proved',
        'runtime_input_semantics': 'unchanged native interpreter symbolic entry-register origins, including exact zero-hook path',
        'dependencies': [list(row) for row in canonical.DIVISION_IDENTITIES],
        'native_runtime_closure': [[site, proof] for site, proof in sorted(closure.items())],
        'native_runtime_frames': native_frames,
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name == '__divsi3'],
        'ordinary_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name != '__divsi3'],
        'ordinary_call_premise': 'conditional: each ordinary callee returns and obeys existing r4-r11/SP preserving direct-call ABI; no native ordinary-callee proof',
        'caller_facts': 'every call clears caller-saved provenance; no numeric/address/flags result facts supplied',
        'caller_frame_policy': 'strict saved slots, SP, r4-r11 and entry-LR restoration; no local allocation, entry-word, buffer or stack-argument permission',
        'runtime_stack_policy': 'canonical DIV/zero accesses only its own proved frame below caller SP',
        'ordinary_call_stack_bound': None, 'frame': restored, 'partition': partition,
        'instructions': len(instructions), 'body_sha256': sha(data), 'ROM_sha256': sha(rom),
        'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
        'producer_source_sha256': source_pins, 'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('DIV-only inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('DIV-only inventory requires one exact mapped owner')
    data = rom[args.address-0x08000000:int(rows[0]['end'], 16)-0x08000000]
    _, _, _, calls, _ = graph.graph(data, args.address, owner.refine(data, args.address, mapping))
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
