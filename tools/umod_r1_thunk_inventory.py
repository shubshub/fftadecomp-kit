"""Explicit saved-only UMOD48 and conditional canonical-r1 structural inventory."""
import argparse
import hashlib
import json
from pathlib import Path

from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP

import analyze
import function_thunk_profile as thunks
import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations
import umodsi3_profile as remainder
import umod_only_ordinary_inventory as umod
import unsigned_remainder_closure_inventory as complete

SELECTOR = 'umod48-r1-thunk-saved-only-inventory-v1'
SCHEMA = 'thumb-umod48-r1-thunk-saved-only-inventory-v1'
THUNK = '_call_via_r1'
THUNK_ADDRESS = thunks.ALIASES[THUNK]
DIVISOR = 48


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(value):
    return hashlib.sha256(value).hexdigest()


def bind_calls(calls, mapping, address, size, rom_size):
    if type(mapping) is not bytes or type(calls) is not dict or len(calls) != 2 or \
            any(type(value) is not int for value in (address, size, rom_size)) or \
            address % 2 or size <= 0 or not match.ROM_BASE <= address < address + size <= match.ROM_BASE + rom_size or any(
                type(site) is not int or type(target) is not int or site % 2 or
                not address <= site <= address + size - 4 for site, target in calls.items()):
        raise ValueError('UMOD/r1 inventory requires exact complete bounded Thumb call sites')
    aliases = {remainder.ADDRESS: '__umodsi3', THUNK_ADDRESS: THUNK}
    if set(calls.values()) != set(aliases) or THUNK_ADDRESS + 4 > match.ROM_BASE + rom_size:
        raise ValueError('UMOD/r1 inventory requires only one actual UMOD and one canonical r1 thunk')
    return {site: aliases[target] for site, target in sorted(calls.items())}


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('UMOD/r1 inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('UMOD/r1 inventory requires immutable exact ROM and index inputs')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or refinement['word_switches'] or type(calls) is not dict or calls != actual_calls or \
            type(bindings) is not dict or bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('UMOD/r1 inventory requires every actual call and excludes switches/local BL')
    entries, rows = complete.indices(mapping, index)
    if complete.span_record(address, address + len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('UMOD/r1 inventory requires exact dual-index reachable instruction counts')
    degree = {site: 0 for site in instructions}
    for successors in edges.values():
        for target in successors:
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
        raise ValueError('UMOD/r1 inventory excludes local CFG cycles')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    for instruction in instructions.values():
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('UMOD/r1 inventory excludes non-ARMv4T widths')
        if instruction.mnemonic.startswith(('ldm', 'stm')) or \
                match.thumb_stack_adjustment(instruction) is not None or any(
                    operand.type == ARM_OP_MEM and (operand.mem.base == ARM_REG_SP or operand.mem.index == ARM_REG_SP) or
                    instruction.mnemonic not in ('push', 'pop') and operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                    for operand in instruction.operands):
            raise ValueError('UMOD/r1 saved-only inventory excludes allocation, SP accesses/exports and block transfers')
    runtime_sites = {site: target for site, target in calls.items() if target == remainder.ADDRESS}
    divisors = remainder.prove_divisors(instructions, edges, address, runtime_sites)
    if set(divisors.values()) != {DIVISOR}:
        raise ValueError('UMOD/r1 inventory requires the exact CFG-proven constant divisor 48')
    thunk_sites = {site: name for site, name in bindings.items() if name == THUNK}
    dependencies = thunks.dependencies(thunk_sites.values(), rom)
    thunks.verify_literal_bindings(data, address, instructions.values(), calls, mapping, {})
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (thunks, remainder, match.divsi3,
                    match.modsi3, match.ashldi3, match.software_double, match.software_float)):
            raise ValueError('UMOD/r1 inventory cannot materialize runtime or thunk addresses')
    closure, runtime_frames = umod.runtime_closure(rom, mapping, index)
    # UMOD preservation comes from its complete native closure and own-frame
    # proof. The canonical indirect destination retains a conditional ABI.
    restored = frame.prove_frame(instructions, edges, address, {}, calls, runtime_calls=thunk_sites)
    modules = (analyze, thunks, frame, match, owner, graph, operations, remainder,
        umod, complete, match.software_double, match.software_float)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False, 'address': address, 'end': address + len(data),
        'instructions': len(instructions), 'cycles_present': False, 'local_bytes': 0,
        'stack_adjustments': [], 'entry_stack_permissions': [], 'buffer_permissions': [],
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site-address, name] for site, name in sorted(bindings.items()) if name == '__umodsi3'],
        'canonical_thunk_calls': [[site-address, name] for site, name in sorted(thunk_sites.items())],
        'ordinary_calls': [], 'caller_divisors': [[site-address, value] for site, value in sorted(divisors.items())],
        'divisor_policy': 'unchanged all-path unsigned32 constant proof, exactly 48; calls kill caller-saved facts',
        'dependencies': [list(row) for row in remainder.IDENTITIES],
        'native_runtime_closure': closure, 'native_runtime_frames': runtime_frames,
        'runtime_stack_policy': 'complete canonical UMOD/zero closure uses only independently proved own frames below caller SP',
        'runtime_entry_domain': 'unchanged native arbitrary32-bit scalar entry origins including the exact zero-hook path',
        'numeric_input_preconditions': [], 'dividend_requirement': None, 'runtime_numeric_return_facts': [],
        'canonical_thunk_runtime': thunks.RUNTIME, 'canonical_thunk_ABI': thunks.ABI,
        'canonical_thunk_dependencies': dependencies,
        'indirect_callee_native_proof': False, 'indirect_callee_effect_proof': False,
        'indirect_call_premise': 'conditional: the indirect target returns and obeys the existing r4-r11/SP preserving ARM ABI; body, target-state validity, IWRAM effects and memory effects are not proved',
        'caller_facts': 'caller-saved provenance cleared at every call; no numeric, address or flags result facts',
        'caller_frame_policy': 'strict saved-only frame restoring r4-r11/SP/entry-LR; no allocation, entry words, aliases, SP exports or buffers',
        'frame': restored, 'partition': partition,
        'CFG_edges': [[site-address, [target-address for target in successors]] for site, successors in sorted(edges.items())],
        'claim': 'acyclic local structural reached-return inventory with exact UMOD/zero closure and conditional canonical-r1 returning ABI',
        'control_flow_guarantee': 'every reached region has a checked return path; no universal termination claim',
        'arithmetic_C_equivalence': False, 'memory_safety_claim': False, 'termination_claim': False,
        'body_sha256': sha(data), 'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
        'ROM_sha256': sha(rom), 'producer_source_sha256': pins, 'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('UMOD/r1 inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    selected = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(selected) != 1:
        raise ValueError('UMOD/r1 inventory requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(selected[0]['end'], 16)-match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
