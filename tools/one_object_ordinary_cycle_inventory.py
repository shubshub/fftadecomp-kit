"""Explicit one-object-word ordinary-call cyclic structural Thumb inventory."""
import argparse
import hashlib
import json
from pathlib import Path

from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP

import analyze
import framed_switch_inventory as ordinary
import function_thunk_profile as thunks
import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations

SELECTOR = 'one-object-word-ordinary-cycle-inventory-v1'
SCHEMA = 'thumb-one-object-word-ordinary-cycle-inventory-v1'
bind_calls = ordinary.bind_calls


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(value):
    return hashlib.sha256(value).hexdigest()


def refine(data, address, mapping):
    return analyze.refine_function(data, address, json.loads(mapping), max_bytes=len(data),
        max_instructions=len(data)//2, rom_end=0x09000000,
        same_owner_long_branches=True, one_object_word_switch=True)


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('ordinary cyclic switch requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('ordinary cyclic switch requires immutable exact ROM/index inputs')
    entries = owner.validate_span(data, address, rom, mapping, index)
    refinement = refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(
        data, address, refinement, one_object_word_switch=True)
    if branches or type(calls) is not dict or calls != actual_calls or \
            len(refinement['word_switches']) != 1 or \
            refinement['word_switches'][0].get('interposed_words') != 1:
        raise ValueError('ordinary cyclic switch requires one exact one-object-word direct-call CFG')
    selected = next(row for row in entries if int(row['rom'], 16) == address)
    rows = [row.split() for row in index.decode().splitlines()
            if row.split() and row.split()[0] == f'{address:08X}']
    if type(selected.get('instrs')) is not int or selected['instrs'] != len(instructions) or \
            len(rows) != 1 or len(rows[0]) < 4 or int(rows[0][3]) != len(instructions):
        raise ValueError('ordinary cyclic switch requires exact dual-index instruction counts')
    if type(bindings) is not dict or bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('ordinary cyclic switch bindings differ from every actual call')
    degree = {site: 0 for site in instructions}
    for successors in edges.values():
        for target in successors:
            degree[target] += 1
    pending = [site for site in instructions if not degree[site]]
    visited = 0
    while pending:
        site = pending.pop()
        visited += 1
        for target in edges[site]:
            degree[target] -= 1
            if not degree[target]:
                pending.append(target)
    if visited == len(instructions):
        raise ValueError('ordinary cyclic switch requires an actual reached CFG cycle')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    if match.uses_stack_frame(instructions.values()):
        raise ValueError('ordinary cyclic switch excludes local stack allocation and SP accesses')
    for instruction in instructions.values():
        if instruction.mnemonic.startswith(('ldm', 'stm')) or any(
                operand.type == ARM_OP_MEM and operand.mem.index == ARM_REG_SP or
                instruction.mnemonic not in ('push', 'pop') and
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in instruction.operands):
            raise ValueError('ordinary cyclic switch excludes stack materialization and block transfers')
    partition = graph.partition(data, address, refinement, instructions, words)
    switch = refinement['word_switches'][0]
    object_word = next(row for row in partition['words'] if row['address'] == address + switch['literal'] - 4)
    if object_word['switch_word'] or not object_word['load_sites']:
        raise ValueError('ordinary cyclic switch requires an actually reached object word load')
    value = object_word['value']
    if not (0x02000000 <= value < 0x04000000 or match.ROM_BASE <= value < match.ROM_BASE + len(rom)):
        raise ValueError('ordinary cyclic switch object word is outside target RAM/ROM')
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (thunks, match.divsi3, match.modsi3,
                    match.umodsi3, match.ashldi3, match.software_double, match.software_float)) or \
                not word['switch_word'] and any(int(row['rom'], 16) & ~1 == value & ~1 for row in entries):
            raise ValueError('ordinary cyclic switch cannot materialize a runtime/thunk/function address')
    # The existing frame-token join must converge and validate every reached
    # return. No iteration bound, path pruning, alias, or buffer permission.
    restored = frame.prove_frame(instructions, edges, address, {}, calls)
    modules = (analyze, ordinary, thunks, frame, match, owner, graph, operations)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False, 'arithmetic_C_equivalence': False,
        'termination_claim': False, 'numeric_input_preconditions': [],
        'address': address, 'end': address + len(data), 'instructions': len(instructions),
        'claim': 'local structural CFG/frame/reached-return inventory under conditional ordinary returning-call ABI',
        'control_flow_guarantee': 'every reached CFG region has a path to a checked return; universal termination is not proved',
        'cycles_present': True, 'loop_iteration_bound': None,
        'frame_policy': 'unchanged strict frame-token fixed point; no locals, aliases, buffer contracts or entry-word permissions',
        'object_word_policy': 'raw authenticated reached ROM literal; no typed source/object extent or ELF relocation admission',
        'object_word': object_word, 'word_switches': refinement['word_switches'],
        'calls': [[site-address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [], 'ordinary_callee_native_proof': False,
        'ordinary_call_premise': 'conditional: every ordinary callee returns and obeys existing r4-r11/SP preserving direct-call ABI',
        'caller_facts': 'caller-saved provenance cleared at every call; no numeric, address, flags or call-result facts granted',
        'memory_safety_claim': False, 'frame': restored, 'partition': partition,
        'body_sha256': sha(data), 'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
        'ROM_sha256': sha(rom), 'producer_source_sha256': pins,
        'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('ordinary cyclic switch manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--' + name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('ordinary cyclic switch requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(rows[0]['end'], 16)-match.ROM_BASE]
    refinement = refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement, one_object_word_switch=True)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
