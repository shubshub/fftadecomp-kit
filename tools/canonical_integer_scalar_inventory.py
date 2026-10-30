"""Explicit structural inventory of canonical integer calls and strict scalar frames."""
import argparse
import hashlib
import json
from pathlib import Path

import div_only_ordinary_inventory as division
import zero_aware_unsigned_quotient_inventory as quotient
import udiv_constant_choices_inventory as unsigned_frames
import umod_only_ordinary_inventory as unsigned_remainder
import software_double_profile as canonical

SELECTOR = 'canonical-integer-scalar-inventory-v1'
SCHEMA = 'thumb-canonical-integer-scalar-inventory-v1'
ZERO = 0x0814274C
OPERATIONS = {'__divsi3': 0x081426B8, '__modsi3': 0x08142950,
              '__udivsi3': 0x08142AB0, '__umodsi3': 0x08142B28}
# Exact complete canonical entry, end and reached return alternatives.
SPECS = {
    '__divsi3': (0x0814274A, (0x0814273E, 0x08142748)),
    '__modsi3': (0x08142A1E, (0x08142A12, 0x08142A1C)),
    '__udivsi3': (0x08142B28, (0x08142B1C, 0x08142B26)),
    '__umodsi3': (0x08142BE8, (0x08142B32, 0x08142BAE, 0x08142BDC, 0x08142BE6)),
}


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def bind_calls(calls, mapping, address, size, rom_size):
    import match
    import function_thunk_profile as thunks
    if type(mapping) is not bytes or type(address) is not int or address % 2 or \
            type(size) is not int or size <= 0 or size % 2 or type(rom_size) is not int or \
            not match.ROM_BASE <= address < address + size <= match.ROM_BASE + rom_size or \
            type(calls) is not dict or not calls or any(
                type(site) is not int or type(target) is not int or site % 2 or target % 2 or
                not address <= site <= address + size - 4 for site, target in calls.items()):
        raise ValueError('canonical integer inventory requires exact typed actual call sites')
    entries, names = json.loads(mapping), {target: name for name, target in OPERATIONS.items()}
    bindings = {}
    for site, target in sorted(calls.items()):
        if target in names:
            bindings[site] = names[target]
            continue
        if thunks.reserved(target):
            raise ValueError('canonical integer ordinary calls exclude reserved call thunks')
        name = f'func_{target:08X}'
        actual = match.function_address_target(name, entries, address, size, rom_size)
        row = next(row for row in entries if int(row['rom'], 16) == actual)
        end = int(row['end'], 16)
        if not actual < end <= match.ROM_BASE + rom_size or \
                actual < address + size and end > address or any(
                    other is not row and int(other['rom'], 16) < end and
                    int(other['end'], 16) > actual for other in entries):
            raise ValueError('ordinary call requires a unique nonoverlapping mapped target span')
        bindings[site] = name
    if not set(bindings.values()) & OPERATIONS.keys():
        raise ValueError('canonical integer inventory requires at least one actual canonical integer call')
    return bindings


def remainder_frames(rom, mapping, closure):
    """Apply the unchanged strict frame engine to MOD and its actual zero call."""
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    from capstone.arm import ARM_OP_MEM, ARM_REG_SP, ARM_REG_R4, ARM_REG_R11
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11 + 1))
    proven = {}
    for address, end in ((ZERO, ZERO + 2), (OPERATIONS['__modsi3'], SPECS['__modsi3'][0])):
        data = rom[address - 0x08000000:end - 0x08000000]
        instructions, edges, branches, calls, words = graph.graph(
            data, address, owner.refine(data, address, mapping))
        if branches or words or any(target not in proven for target in calls.values()) or any(
                operand.mem.base != ARM_REG_SP or operand.mem.index
                for instruction in instructions.values() for operand in instruction.operands
                if operand.type == ARM_OP_MEM):
            raise ValueError('canonical MOD frame requires exact dependencies and stack-only accesses')
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
                                    call_preservation={site: preserved for site in calls})
        if restored['returns'] != closure[address]['returns']:
            raise ValueError('canonical MOD frame return coverage differs')
        proven[address] = {'frame': restored, 'maximum_additional_stack_bytes':
            restored['maximum_frame_bytes'] + max(
                (proven[target]['maximum_additional_stack_bytes'] for target in calls.values()), default=0),
            'caller_memory_writes': [], 'caller_stack_reads': [], 'restores': 'r4-r11,sp,entry-lr'}
    return [[address, proof] for address, proof in sorted(proven.items())]


def prove_called_closures(rom, mapping, index, families):
    """Dispatch only actual families; each existing factory also proves zero."""
    closures, frames, components = {}, {}, []
    for name in sorted(families):
        if name == '__divsi3':
            proof = canonical.prove_division_closure(rom, mapping, index)
            restored = division.runtime_frames(rom, mapping, proof)
        elif name == '__modsi3':
            proof = canonical.prove_remainder_closure(rom, mapping, index)
            restored = remainder_frames(rom, mapping, proof)
        elif name == '__udivsi3':
            proof = quotient.prove_quotient_closure(rom, mapping, index)
            restored = unsigned_frames.runtime_frames(rom, mapping, proof)
        elif name == '__umodsi3':
            raw, restored = unsigned_remainder.runtime_closure(rom, mapping, index)
            proof = dict(raw)
        else:
            raise ValueError('unsupported canonical integer family')
        restored = dict(restored)
        target = OPERATIONS[name]
        expected = {target, ZERO}
        if set(proof) != expected or set(restored) != expected or \
                proof[target]['returns'] != list(SPECS[name][1]) or \
                proof[ZERO]['returns'] != [ZERO] or any(
                    record['writes'] or record['stack_reads'] for record in proof.values()):
            raise ValueError('canonical integer inventory requires exact complete runtime/zero returns and effects')
        for site in sorted(expected):
            if restored[site]['frame']['returns'] != proof[site]['returns'] or \
                    restored[site]['caller_memory_writes'] or restored[site]['caller_stack_reads']:
                raise ValueError('canonical integer native and frame returns/effects differ')
            if site in closures and (closures[site] != proof[site] or frames[site] != restored[site]):
                raise ValueError('canonical integer shared zero native/frame proofs differ')
            closures[site], frames[site] = proof[site], restored[site]
        components.append({'family': name, 'closure_factory_invocations': 1,
                           'native_runtime_components': 2, 'strict_runtime_frame_components': 2})
    return closures, frames, components


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    import function_thunk_profile as thunks
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('canonical integer inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or \
            type(address) is not int or type(calls) is not dict or type(bindings) is not dict:
        raise ValueError('canonical integer inventory requires immutable exact bytes and typed call records')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('canonical integer inventory requires exact complete direct-call CFG and bindings')
    entries, rows = canonical.indices(mapping, index)
    if canonical.span_record(address, address + len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('canonical integer caller dual-index count differs from complete CFG')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    adjustments = []
    for instruction in instructions.values():
        adjustment = match.thumb_stack_adjustment(instruction)
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('canonical integer inventory excludes non-ARMv4T widths')
        if instruction.mnemonic.startswith(('ldm', 'stm')) or any(
                operand.type == ARM_OP_MEM and (operand.mem.index == ARM_REG_SP or
                    operand.mem.base == ARM_REG_SP and (operand.mem.index or
                    instruction.mnemonic not in ('ldr', 'str') or operand.mem.disp % 4)) or
                instruction.mnemonic not in ('push', 'pop') and adjustment is None and
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in instruction.operands):
            raise ValueError('canonical integer scalar frame excludes SP addresses, nonword locals and block transfers')
        if adjustment is not None:
            adjustments.append([instruction.address, adjustment])
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or thunks.reserved(value) or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (match.divsi3, match.modsi3, match.umodsi3,
                    match.ashldi3, match.software_double, match.software_float)):
            raise ValueError('canonical integer inventory cannot materialize runtime or thunk addresses')
    # Default strict scalar frame fixpoint, with no alias/entry/buffer opt-in.
    restored = frame.prove_frame(instructions, edges, address, {}, calls)
    if restored['maximum_frame_bytes'] <= 0:
        raise ValueError('canonical integer inventory requires an allocated-or-saved caller frame')
    families = set(bindings.values()) & OPERATIONS.keys()
    closure, native_frames, components = prove_called_closures(rom, mapping, index, families)
    modules = (match, thunks, owner, graph, operations, frame, canonical, division,
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
        'caller_frame_policy': 'strict scalar word locals, saved slots, r4-r11/SP/entry-LR restoration; no SP address, entry-word, local-alias or buffer permission',
        'runtime_stack_policy': 'each canonical runtime accesses only its independently proved abstract frame below current caller SP; no caller writes or stack reads',
        'external_memory_effect_boundary': 'ordinary non-SP scalar memory operations retain existing structural policy; physical addresses, nonalias and memory safety are not proved',
        'stack_adjustments_in_words': adjustments, 'backward_edges': [[site, target]
            for site, targets in sorted(edges.items()) for target in targets if target <= site],
        'frame': restored, 'partition': partition, 'instructions': len(instructions),
        'address': address, 'end': address+len(data), 'body_sha256': sha(data),
        'mapping_sha256': sha(mapping), 'index_sha256': sha(index), 'ROM_sha256': sha(rom),
        'producer_source_sha256': source_pins}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('canonical integer inventory manifest differs from fresh native proof')
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
        raise ValueError('canonical integer inventory requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(selected[0]['end'], 16)-match.ROM_BASE]
    _, _, _, calls, _ = graph.graph(data, args.address, owner.refine(data, args.address, mapping))
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
