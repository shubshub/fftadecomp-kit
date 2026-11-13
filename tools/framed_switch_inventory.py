"""Explicit structural inventory for one ordinary-call scalar-frame Thumb switch."""
import argparse
import hashlib
import json
from pathlib import Path

from capstone.arm import ARM_OP_REG, ARM_REG_SP

import analyze
import function_thunk_profile as thunks
import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations

THUNK_SELECTOR = 'scalar-frame-r3-thunk-switch-inventory-v1'
THUNK_SCHEMA = 'thumb-scalar-frame-r3-thunk-switch-inventory-v1'
NUMERIC_THUNK_SELECTOR = 'scalar-frame-r3-thunk-numeric-switch-inventory-v1'
NUMERIC_THUNK_SCHEMA = 'thumb-scalar-frame-r3-thunk-numeric-switch-inventory-v1'
THUNK_SELECTORS = (THUNK_SELECTOR, NUMERIC_THUNK_SELECTOR)
SELECTOR = 'scalar-frame-ordinary-switch-inventory-v1'
SCHEMA = 'thumb-scalar-frame-ordinary-switch-inventory-v1'
CYCLIC_SELECTOR = 'scalar-frame-ordinary-cyclic-switch-inventory-v1'
CYCLIC_SCHEMA = 'thumb-scalar-frame-ordinary-cyclic-switch-inventory-v1'
ENTRY_SELECTOR = 'scalar-entry-word-ordinary-switch-inventory-v1'
ENTRY_SCHEMA = 'thumb-scalar-entry-word-ordinary-switch-v1'
ENTRY_DATA_SELECTOR = 'scalar-entry-two-words-data-ordinary-switch-inventory-v1'
ENTRY_DATA_SCHEMA = 'thumb-scalar-entry-two-words-data-ordinary-switch-v1'


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(value):
    return hashlib.sha256(value).hexdigest()


def bind_calls(calls, mapping, address, size, rom_size, *, allow_r3=False):
    """Centrally bind every actual ordinary site, excluding runtime/thunk aliases."""
    if type(mapping) is not bytes or type(calls) is not dict or not calls or any(
            type(value) is not int for value in (address, size, rom_size)) or any(
            type(site) is not int or type(target) is not int or site % 2 or
            not address <= site <= address + size - 4 for site, target in calls.items()):
        raise ValueError('scalar switch requires exact ordinary call boundaries')
    if type(allow_r3) is not bool:
        raise ValueError('scalar thunk permission must be explicit Boolean')
    entries = json.loads(mapping)
    bindings = {}
    for site, target in sorted(calls.items()):
        if allow_r3 and target == thunks.ALIASES['_call_via_r3']:
            bindings[site] = '_call_via_r3'
            continue
        if thunks.reserved(target):
            raise ValueError('scalar switch excludes reserved call thunks')
        name = f'func_{target:08X}'
        actual = match.function_address_target(name, entries, address, size, rom_size)
        row = next(row for row in entries if int(row['rom'], 16) == actual)
        end = int(row['end'], 16)
        if not actual < end <= match.ROM_BASE + rom_size or \
                actual < address + size and end > address or any(
                    other is not row and int(other['rom'], 16) < end and
                    int(other['end'], 16) > actual for other in entries):
            raise ValueError('scalar switch requires unique nonoverlapping ordinary target spans')
        bindings[site] = name
    return bindings


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector not in (SELECTOR,CYCLIC_SELECTOR,ENTRY_SELECTOR,ENTRY_DATA_SELECTOR,*THUNK_SELECTORS):
        raise ValueError('scalar switch requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('scalar switch requires immutable exact ROM and index inputs')
    entries = owner.validate_span(data, address, rom, mapping, index)
    numeric = selector == NUMERIC_THUNK_SELECTOR
    refinement = owner.refine(data, address, mapping, one_numeric_word_switch=numeric)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement,
        one_numeric_word_switch=numeric)
    if branches or len(refinement['word_switches']) != 1 or \
            refinement['word_switches'][0].get('interposed_words', 0) != (1 if numeric else 0) or \
            type(calls) is not dict or calls != actual_calls:
        raise ValueError('scalar switch requires one exact switch with its selected interposed words and ordinary calls')
    numeric_word = None
    if numeric:
        import one_constant_scalar_switch_inventory as constant_switch
        constant_switch.guard_predecessors(instructions, edges, address, refinement['word_switches'][0])
    expected = bind_calls(calls, mapping, address, len(data), len(rom),
        allow_r3=selector in THUNK_SELECTORS)
    if type(bindings) is not dict or bindings != expected:
        raise ValueError('scalar switch bindings differ from every actual call')
    runtime_calls = {site: name for site, name in expected.items() if name == '_call_via_r3'}
    if selector in THUNK_SELECTORS and (not runtime_calls or len(runtime_calls) == len(expected)):
        raise ValueError('scalar thunk switch requires actual canonical R3 and ordinary calls')
    dependencies = thunks.dependencies(runtime_calls.values(), rom) if runtime_calls else []
    selected = next(row for row in entries if int(row['rom'], 16) == address)
    rows = [line.split() for line in index.decode().splitlines()
            if line.split() and line.split()[0] == f'{address:08X}']
    if type(selected.get('instrs')) is not int or selected['instrs'] != len(instructions) or \
            len(rows) != 1 or len(rows[0]) < 4 or int(rows[0][3]) != len(instructions):
        raise ValueError('scalar switch requires exact dual-index reachable instruction counts')
    # Keep the existing acyclic inventory boundary. This composition grants no
    # loop permission or runtime iteration bound.
    indegree = {site: 0 for site in instructions}
    for successors in edges.values():
        for target in successors:
            indegree[target] += 1
    pending = [site for site in instructions if not indegree[site]]
    reached = 0
    while pending:
        site = pending.pop()
        reached += 1
        for target in edges[site]:
            indegree[target] -= 1
            if not indegree[target]:
                pending.append(target)
    if selector in (SELECTOR, *THUNK_SELECTORS) and reached != len(instructions):
        raise ValueError('scalar switch excludes local CFG cycles')
    partition = graph.partition(data, address, refinement, instructions, words)
    if numeric:
        numeric_word = next((word for word in partition['words']
            if word['address'] == address + refinement['word_switches'][0]['literal'] - 4), None)
        if numeric_word is None or numeric_word['switch_word'] or not numeric_word['load_sites'] or \
                not 0 <= numeric_word['value'] <= 0xffff:
            raise ValueError('numeric thunk switch requires an actually reached u16 interposed literal')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    adjustments = []
    for site, instruction in sorted(instructions.items()):
        adjustment = match.thumb_stack_adjustment(instruction)
        if instruction.mnemonic.startswith(('ldm', 'stm')):
            raise ValueError('scalar switch excludes block transfers')
        if instruction.mnemonic not in ('push', 'pop') and adjustment is None and any(
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in instruction.operands):
            raise ValueError('scalar switch excludes stack-address materialization')
        if adjustment is not None:
            adjustments.append([site - address, adjustment * 4])
    if selector not in (ENTRY_SELECTOR, ENTRY_DATA_SELECTOR) and not any(value < 0 for _, value in adjustments):
        raise ValueError('scalar switch requires an actual nonzero fixed local allocation')
    # No buffer contracts, entry-word permissions, alias policies or call
    # preservation overrides. Every return restores the original frame tokens.
    entry_policy = None
    if selector == ENTRY_SELECTOR:
        import readonly_entry_stack_profile as entry_stack
        entry_policy = dict(schema=entry_stack.SCHEMA, words=[0])
    elif selector == ENTRY_DATA_SELECTOR:
        import readonly_entry_stack_words_profile as entry_stack
        entry_policy = dict(schema=entry_stack.SCHEMA, words=[0, 1])
    restored = frame.prove_frame(instructions, edges, address, branches, calls,
        entry_stack_policy=entry_policy, runtime_calls=runtime_calls or None)
    if entry_policy is not None and not restored['entry_stack']['reads']:
        raise ValueError('entry-word switch requires an actual incoming word0 read')
    modules = (analyze, thunks, frame, match, owner, graph, operations)
    if entry_policy is not None:
        modules += (entry_stack,)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': THUNK_SCHEMA if selector == THUNK_SELECTOR else NUMERIC_THUNK_SCHEMA if numeric else ENTRY_DATA_SCHEMA if selector == ENTRY_DATA_SELECTOR else ENTRY_SCHEMA if selector == ENTRY_SELECTOR else CYCLIC_SCHEMA if selector == CYCLIC_SELECTOR else SCHEMA, 'selector': selector, 'inventory_only': True,
        'source_or_ELF_admission': False, 'address': address, 'end': address + len(data),
        'instructions': len(instructions), 'word_switches': refinement['word_switches'],
        'interposed_constant_words': 1 if numeric else 0, 'stack_adjustments': adjustments,
        'calls': [[site - address, name] for site, name in sorted(bindings.items()) if site not in runtime_calls],
        'runtime_calls': [[site-address, name] for site, name in sorted(runtime_calls.items())], 'ordinary_callee_native_proof': False,
        'ordinary_call_premise': 'conditional: every ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI',
        'caller_facts': 'caller-saved register provenance cleared at every call; no numeric, address, or flags result facts',
        'frame': restored, 'partition': partition,
        'claim': 'complete local structural CFG/frame/return inventory under conditional ordinary returning-call ABI',
        'numeric_input_preconditions': [], 'arithmetic_C_equivalence': False,
        'termination_claim': False,
        'control_flow_guarantee': ('every reached return restores the frame; local cycles receive no termination or iteration-bound claim' if selector in (CYCLIC_SELECTOR, ENTRY_SELECTOR, ENTRY_DATA_SELECTOR) else 'every reached CFG region has a path to a checked return; universal termination is not proved'),
        'body_sha256': sha(data), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'ROM_sha256': sha(rom),
        'producer_source_sha256': pins, 'complete_native_structural_proof': True}
    if selector in (CYCLIC_SELECTOR, ENTRY_SELECTOR, ENTRY_DATA_SELECTOR):
        observed['local_CFG_cycles'] = reached != len(instructions)
    if numeric:
        observed['numeric_word'] = numeric_word
    if selector in THUNK_SELECTORS:
        observed['canonical_thunks'] = dict(ABI=thunks.ABI, dependencies=dependencies,
            contract='conditional compatible returning indirect ABI; no callback identity or memory-effect theorem')
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('scalar switch manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    parser.add_argument('--rom', required=True, type=Path)
    parser.add_argument('--mapping', required=True, type=Path)
    parser.add_argument('--index', required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('scalar switch requires one exact mapped owner')
    data = rom[args.address - match.ROM_BASE:int(rows[0]['end'], 16) - match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
