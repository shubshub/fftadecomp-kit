"""Explicit saved-only unsigned DIV/MOD, canonical-thunk and ordinary-call inventory.

This composes the existing complete native UDIV/UMOD/zero closure with the
canonical ``_call_via_rN`` thunk ABI.  Every runtime call must receive a
CFG-proven nonzero unsigned32 constant divisor in r1.  Each indirect callee
keeps the conditional returning ABI of the existing thunk selectors: its
body, value and effects stay opaque.
"""
import argparse
import hashlib
import json
from pathlib import Path

import unsigned_divmod_ordinary_inventory as divmod

SELECTOR = 'unsigned-divmod-thunk-ordinary-structural-inventory-v1'
SCHEMA = 'thumb-unsigned-divmod-thunk-ordinary-structural-inventory-v1'
OPERATIONS = dict(divmod.OPERATIONS)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def reserved_target(target):
    import match
    import function_thunk_profile as thunks
    import umodsi3_profile as remainder
    return target in match.RUNTIME_HELPERS.values() or thunks.reserved(target) or \
        match.is_udivsi3_address(target) or any(module.reserved(target) for module in (
            remainder, match.divsi3, match.modsi3, match.ashldi3,
            match.software_double, match.software_float))


def bind_calls(calls, mapping, address, size, rom_size):
    """Name every actual call: canonical runtime, canonical thunk or ordinary."""
    import match
    import function_thunk_profile as thunks
    if type(mapping) is not bytes or type(address) is not int or address % 2 or \
            type(size) is not int or size <= 0 or type(rom_size) is not int or \
            not match.ROM_BASE <= address < address+size <= match.ROM_BASE+rom_size or \
            type(calls) is not dict or any(
                type(site) is not int or type(target) is not int or site % 2 or
                not address <= site <= address+size-4 for site, target in calls.items()):
        raise ValueError('unsigned DIV/MOD thunks require exact complete bounded Thumb call sites')
    entries = json.loads(mapping)
    runtimes = {target: name for name, target in OPERATIONS.items()}
    aliases = {target: name for name, target in thunks.ALIASES.items()}
    bindings = {}
    for site, target in sorted(calls.items()):
        if target in runtimes:
            bindings[site] = runtimes[target]
            continue
        if target in aliases:
            if target + 4 > match.ROM_BASE + rom_size:
                raise ValueError('canonical thunk lies outside the ROM')
            bindings[site] = aliases[target]
            continue
        if reserved_target(target):
            raise ValueError('unsigned DIV/MOD thunks exclude noncanonical runtime or thunk targets')
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
    names = set(bindings.values())
    if not names & set(OPERATIONS) or not names & set(thunks.ALIASES):
        raise ValueError('unsigned DIV/MOD thunks require an actual canonical runtime and thunk call')
    return bindings


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    import match
    import function_thunk_profile as thunks
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    import local_long_branch_profile as frame
    import umodsi3_profile as remainder
    import unsigned_remainder_closure_inventory as complete
    from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('unsigned DIV/MOD thunks require their explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('unsigned DIV/MOD thunks require immutable exact ROM and dual-index bytes')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or refinement['word_switches'] or type(calls) is not dict or calls != actual_calls or \
            type(bindings) is not dict or bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('unsigned DIV/MOD thunks require the exact complete direct-call CFG and bindings')
    entries, rows = complete.indices(mapping, index)
    if complete.span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('unsigned DIV/MOD thunk caller dual-index count differs from native CFG')
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
        raise ValueError('unsigned DIV/MOD thunks exclude local CFG cycles')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    for instruction in instructions.values():
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('unsigned DIV/MOD thunks exclude non-ARMv4T instruction widths')
        if instruction.mnemonic.startswith(('ldm', 'stm')) or \
                match.thumb_stack_adjustment(instruction) is not None or any(
                    operand.type == ARM_OP_MEM and (operand.mem.base == ARM_REG_SP or operand.mem.index == ARM_REG_SP) or
                    instruction.mnemonic not in ('push', 'pop') and operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                    for operand in instruction.operands):
            raise ValueError('unsigned DIV/MOD thunk saved-only frame excludes locals, entry words and SP exports')
    runtime_sites = {site: name for site, name in bindings.items() if name in OPERATIONS}
    thunk_sites = {site: name for site, name in bindings.items() if name in thunks.ALIASES}
    divisors = remainder.prove_divisors(instructions, edges, address, runtime_sites)
    if set(divisors) != set(runtime_sites):
        raise ValueError('unsigned DIV/MOD thunks require a CFG-proven divisor at every runtime call')
    dependencies = thunks.dependencies(thunk_sites.values(), rom)
    thunks.verify_literal_bindings(data, address, instructions.values(), calls, mapping, {})
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        if reserved_target(word['value']):
            raise ValueError('unsigned DIV/MOD thunks cannot materialize runtime or thunk addresses')
    closure, runtime_frames = divmod.runtime_closure(rom, mapping, index)
    # Runtime preservation comes from the complete native closure; ordinary
    # and indirect callees keep the existing conditional returning ABI.  The
    # frame proof also refuses an indirect target with stack or entry-LR
    # provenance.
    restored = frame.prove_frame(instructions, edges, address, {}, calls,
        runtime_calls={site: name for site, name in bindings.items()
                       if name == '__udivsi3' or name in thunks.ALIASES})
    ordinary = [[site-address, name] for site, name in sorted(bindings.items())
                if name not in OPERATIONS and name not in thunks.ALIASES]
    modules = (match, thunks, owner, graph, operations, frame, complete, remainder, divmod,
        divmod.quotient, divmod.remainder, match.software_double, match.software_float)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True, 'source_or_ELF_admission': False,
        'claim': 'acyclic local structural CFG/frame and restoration at every reached return',
        'arithmetic_C_equivalence': False, 'memory_safety_claim': False, 'termination_claim': False,
        'physical_memory_nonalias_claim': False, 'runtime_numeric_return_facts': [],
        'runtime_entry_domain': 'unchanged native interpreter arbitrary32-bit scalar entry origins, including real zero paths',
        'numeric_input_preconditions': [], 'entry_stack_contract': None, 'cycles_present': False,
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site-address, name] for site, name in sorted(runtime_sites.items())],
        'caller_divisors': [[site-address, divisors[site]] for site in sorted(divisors)],
        'divisor_policy': 'unchanged all-path unsigned32 nonzero constant proof in r1 at every runtime call; calls kill caller-saved facts',
        'canonical_thunk_calls': [[site-address, name] for site, name in sorted(thunk_sites.items())],
        'canonical_thunk_runtime': thunks.RUNTIME, 'canonical_thunk_ABI': thunks.ABI,
        'canonical_thunk_dependencies': dependencies,
        'indirect_callee_native_proof': False, 'indirect_callee_effect_proof': False,
        'indirect_call_premise': 'conditional: each indirect target returns and obeys the existing r4-r11/SP preserving ARM ABI; body, value, target-state validity and memory effects are not proved',
        'ordinary_calls': ordinary, 'ordinary_call_premise': (
            'conditional: each ordinary callee returns and obeys existing r4-r11/SP/entry-LR preserving direct-call ABI; no native callee or memory-effects proof'
            if ordinary else None),
        'caller_frame_policy': 'saved-only strict frame; no allocated locals, entry words, stack aliases or SP exports',
        'caller_facts': 'calls kill caller-saved provenance; no numeric return, address or flags facts',
        'runtime_stack_policy': 'canonical UDIV/UMOD/zero access only independently proved frames below caller SP',
        'native_runtime_closure': closure, 'native_runtime_frames': runtime_frames, 'shared_zero_identity_equal': True,
        'dependencies': {'quotient': [list(row) for row in match.UDIVSI3_IDENTITIES],
            'remainder': [list(row) for row in remainder.IDENTITIES]},
        'frame': restored, 'partition': partition, 'instructions': len(instructions), 'address': address,
        'end': address+len(data), 'body_sha256': sha(data), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'ROM_sha256': sha(rom), 'producer_source_sha256': pins,
        'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('unsigned DIV/MOD thunk manifest differs from fresh native proof')
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
        raise ValueError('unsigned DIV/MOD thunks require one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(rows[0]['end'], 16)-match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
