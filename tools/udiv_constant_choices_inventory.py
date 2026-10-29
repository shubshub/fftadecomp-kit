"""Explicit finite-choice UDIV structural inventory with conditional ordinary calls."""
import argparse
import hashlib
import json
from pathlib import Path

import zero_aware_unsigned_quotient_inventory as quotient

SELECTOR = 'udiv-constant-choices-ordinary-inventory-v1'
SCHEMA = 'thumb-udiv-constant-choices-ordinary-inventory-v1'
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
        raise ValueError('UDIV choices inventory requires exact complete actual call sites')
    entries = json.loads(mapping)
    bindings = {}
    for site, target in sorted(calls.items()):
        if target == quotient.UDIV:
            bindings[site] = '__udivsi3'
            continue
        if thunks.reserved(target):
            raise ValueError('UDIV choices ordinary calls exclude reserved call thunks')
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
    if '__udivsi3' not in bindings.values() or not any(name != '__udivsi3' for name in bindings.values()):
        raise ValueError('UDIV choices inventory requires actual UDIV and ordinary calls')
    return bindings


def prove_divisor_choices(instructions, edges, address, calls):
    """Forward must-definition proof with finite unions, never assumed inputs.

    An absent fact is unknown, including any uninitialized incoming path. Only
    exact unconditional Thumb immediate MOV and register copies generate facts.
    Every other register write kills its fact; every call kills caller-saved
    registers. Joins union at most two constants only for registers defined on
    every incoming path. Checks use converged states over the full reached CFG.
    """
    from capstone.arm import (ARM_CC_AL, ARM_CC_INVALID, ARM_REG_R0,
                              ARM_REG_R1, ARM_REG_R3, ARM_REG_R12, ARM_REG_LR)
    sites = {site for site, target in calls.items() if target == quotient.UDIV}
    if address not in instructions or set(edges) != set(instructions) or not sites or \
            set(calls) - set(instructions):
        raise ValueError('UDIV choices require exact complete reached instruction and call sites')
    states, pending = {address: {}}, [address]
    while pending:
        site = pending.pop()
        instruction, incoming = instructions[site], states[site]
        outgoing = dict(incoming)
        _, written = instruction.regs_access()
        for register in written:
            outgoing.pop(register, None)
        if site in calls:
            for register in (*range(ARM_REG_R0, ARM_REG_R3+1), ARM_REG_R12, ARM_REG_LR):
                outgoing.pop(register, None)
        elif instruction.size == 2 and instruction.cc in (ARM_CC_AL, ARM_CC_INVALID):
            half = int.from_bytes(instruction.bytes, 'little')
            destination, source, value = None, None, None
            if half & 0xF800 == 0x2000:  # MOVS Rd,#imm8
                destination, value = ARM_REG_R0+((half >> 8) & 7), frozenset((half & 255,))
            elif half & 0xFFC0 == 0x1C00 or half & 0xFFC0 == 0:  # ADDS/LSLS #0 copy
                destination, source = ARM_REG_R0+(half & 7), ARM_REG_R0+((half >> 3) & 7)
            elif half & 0xFF00 == 0x4600:  # exact non-flag-writing high-register MOV
                dst, src = (half & 7) | ((half >> 4) & 8), (half >> 3) & 15
                if dst < 13 and src < 13:
                    destination, source = ARM_REG_R0+dst, ARM_REG_R0+src
            if source is not None:
                value = incoming.get(source)
            if destination is not None and value is not None:
                outgoing[destination] = value
        for successor in edges[site]:
            if successor not in instructions:
                raise ValueError('UDIV choices CFG leaves exact instruction boundaries')
            previous = states.get(successor)
            merged = dict(outgoing) if previous is None else {
                register: previous[register] | outgoing[register]
                for register in previous.keys() & outgoing.keys()
                if len(previous[register] | outgoing[register]) <= 2}
            if previous != merged:
                states[successor] = merged
                pending.append(successor)
    if set(states) != set(instructions):
        raise ValueError('UDIV choices do not cover every reached instruction')
    proven = {}
    for site in sorted(sites):
        values = states[site].get(ARM_REG_R1)
        if not values or not values <= frozenset((4, 8)):
            raise ValueError(f'UDIV requires all-path defined r1 choices within {{4,8}} at {site:08X}')
        proven[site] = sorted(values)
    return proven


def runtime_frames(rom, mapping, closure):
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    from capstone.arm_const import ARM_REG_R4, ARM_REG_R11
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11+1))
    proven = {}
    for address, end in ((ZERO, ZERO+2), (quotient.UDIV, 0x08142B28)):
        data = rom[address-0x08000000:end-0x08000000]
        refinement = owner.refine(data, address, mapping)
        instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
        if branches or words or any(target not in proven for target in calls.values()) or \
                closure[address]['writes'] or closure[address]['stack_reads']:
            raise ValueError('UDIV choices runtime requires exact dependencies and no caller-memory effects')
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
                                    call_preservation={site: preserved for site in calls})
        if restored['returns'] != closure[address]['returns']:
            raise ValueError('UDIV choices runtime frame return coverage differs')
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
        raise ValueError('UDIV choices inventory requires its explicit inventory-only selector')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('UDIV choices inventory requires its exact complete direct-call CFG and bindings')
    entries, rows = canonical.indices(mapping, index)
    if canonical.span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('UDIV choices inventory requires exact dual-index reachable instruction counts')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    if match.uses_stack_frame(instructions.values()):
        raise ValueError('UDIV choices inventory requires a caller without allocated locals')
    choices = prove_divisor_choices(instructions, edges, address, calls)
    restored = frame.prove_frame(instructions, edges, address, {}, calls)
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or match.function_thunk.reserved(value) or \
                match.is_udivsi3_address(value) or any(module.reserved(value) for module in
                (match.divsi3, match.modsi3, match.umodsi3, match.ashldi3, canonical, native)):
            raise ValueError('UDIV choices inventory cannot materialize runtime or thunk addresses')
    closure = quotient.prove_quotient_closure(rom, mapping, index)
    if set(closure) != {quotient.UDIV, ZERO} or \
            closure[quotient.UDIV]['returns'] != [0x08142B1C, 0x08142B26] or \
            closure[ZERO]['returns'] != [ZERO] or any(
                proof['writes'] or proof['stack_reads'] for proof in closure.values()):
        raise ValueError('UDIV choices inventory requires complete exact UDIV/zero native closures')
    native_frames = runtime_frames(rom, mapping, closure)
    modules = (match, owner, graph, operations, frame, canonical, native, quotient)
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False,
        'claim': 'structural target-state ABI/effects at reached returns under exact UDIV/zero closure and conditional ordinary returning-call ABI',
        'runtime_entry_domain': 'arbitrary32-bit entry-register patterns; no numeric preconditions',
        'arithmetic_C_equivalence': False, 'memory_safety_claim': False,
        'runtime_numeric_return_facts': [], 'numeric_operand_preconditions': [], 'nonzero_facts': [],
        'termination_claim': False,
        'control_flow_guarantee': 'every reached CFG region has a path to a checked return; universal termination is not proved',
        'runtime_input_semantics': 'unchanged native interpreter symbolic entry-register origins, including exact zero-hook path',
        'dependencies': [[quotient.UDIV, 0x08142B28, sha(rom[quotient.UDIV-match.ROM_BASE:0x08142B28-match.ROM_BASE])],
                         [ZERO, ZERO+2, sha(rom[ZERO-match.ROM_BASE:ZERO+2-match.ROM_BASE])]],
        'permitted_divisor_constants': [4, 8],
        'derived_divisor_choices': [[site-address, values] for site, values in sorted(choices.items())],
        'divisor_policy': 'all reaching paths define r1 as 4 or 8; no entry-register or callee-result numeric premise',
        'native_runtime_closure': [[site, proof] for site, proof in sorted(closure.items())],
        'native_runtime_frames': native_frames,
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name == '__udivsi3'],
        'ordinary_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name != '__udivsi3'],
        'ordinary_call_premise': 'conditional: each ordinary callee returns and obeys existing r4-r11/SP preserving direct-call ABI; no native ordinary-callee proof',
        'caller_facts': 'every call clears caller-saved provenance; no numeric/address/flags result facts supplied',
        'caller_frame_policy': 'strict saved slots, SP, r4-r11 and entry-LR restoration; no local allocation, entry-word, buffer or stack-argument permission',
        'runtime_stack_policy': 'canonical UDIV/zero accesses only its own proved frame below caller SP',
        'ordinary_call_stack_bound': None, 'frame': restored, 'partition': partition,
        'instructions': len(instructions), 'body_sha256': sha(data), 'ROM_sha256': sha(rom),
        'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
        'producer_source_sha256': source_pins, 'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('UDIV choices inventory manifest differs from fresh native proof')
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
        raise ValueError('UDIV choices inventory requires one exact mapped owner')
    data = rom[args.address-0x08000000:int(rows[0]['end'], 16)-0x08000000]
    _, _, _, calls, _ = graph.graph(data, args.address, owner.refine(data, args.address, mapping))
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
