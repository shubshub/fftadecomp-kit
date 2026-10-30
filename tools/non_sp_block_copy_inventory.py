"""Explicit two-constant scalar-frame non-SP block-copy structural inventory."""
import argparse
import hashlib
import json
from pathlib import Path

from capstone.arm import (ARM_OP_REG, ARM_OP_MEM, ARM_REG_SP, ARM_REG_R0,
                          ARM_REG_R7, ARM_CC_AL, ARM_CC_INVALID)

import analyze
import function_thunk_profile as thunks
import framed_switch_inventory as ordinary
import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations
import switch_constants_profile as constants

SELECTOR = 'non-sp-block-copy-inventory-v1'
SCHEMA = 'thumb-non-sp-block-copy-inventory-v1'


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(value):
    return hashlib.sha256(value).hexdigest()


bind_calls = ordinary.bind_calls


def refine(data, address, mapping):
    return analyze.refine_function(data, address, json.loads(mapping), max_bytes=len(data),
        max_instructions=len(data)//2, rom_end=0x09000000,
        same_owner_long_branches=True, two_constant_word_switch=True)


def transfer(instruction):
    """Authenticate only unambiguous ARMv4T Thumb16 increment-after transfers.

    The enclosing unchanged strict frame proof rejects every SP materialization
    and propagates the exact regs_access origin kills validated here. This is no
    claim about the actual external object's extent, alignment or nonaliasing.
    """
    raw = bytes(instruction.bytes)
    if instruction.size != 2 or len(raw) != 2:
        raise ValueError('block copy requires exact Thumb16 encoding')
    encoded = int.from_bytes(raw, 'little')
    base = ARM_REG_R0 + ((encoded >> 8) & 7)
    listed = [ARM_REG_R0 + bit for bit in range(8) if encoded & (1 << bit)]
    load = bool(encoded & 0x0800)
    expected_read = {base} if load else {base, *listed}
    expected_written = {base, *listed} if load else {base}
    read, written = instruction.regs_access()
    if encoded & 0xf000 != 0xc000 or not listed or base in listed or \
            instruction.mnemonic != ('ldm' if load else 'stm') or \
            instruction.cc not in (ARM_CC_AL, ARM_CC_INVALID) or not instruction.writeback or \
            any(op.type != ARM_OP_REG or op.shift.type or op.shift.value or op.subtracted
                for op in instruction.operands) or \
            [op.reg for op in instruction.operands] != [base, *listed] or \
            not all(ARM_REG_R0 <= reg <= ARM_REG_R7 for reg in [base, *listed]) or \
            set(read) != expected_read or set(written) != expected_written:
        raise ValueError('block copy excludes ambiguous writeback, base overlap or unsupported register effects')
    return {'site': instruction.address, 'bytes': raw.hex(), 'operation': instruction.mnemonic,
            'base': instruction.reg_name(base), 'registers': [instruction.reg_name(reg) for reg in listed],
            'writeback_bytes': 4 * len(listed),
            'origin_kills': sorted(instruction.reg_name(reg) for reg in expected_written),
            'flags_written': False}


def guard_predecessors(instructions, edges, address, switch):
    predecessors = {site: set() for site in instructions}
    for site, successors in edges.items():
        for successor in successors:
            predecessors[successor].add(site)
    comparison, guard, dispatch = [address + switch[key] for key in ('comparison', 'guard', 'dispatch')]
    expected = {guard: {comparison}, dispatch: {guard}}
    if dispatch - guard == 4:
        expected[guard + 2] = {guard}
    expected.update({dispatch + distance: {dispatch + distance - 2} for distance in range(2, 10, 2)})
    if comparison not in instructions or any(site == address or predecessors.get(site) != incoming
                                              for site, incoming in expected.items()):
        raise ValueError('block-copy switch bound is bypassed by an unverified predecessor')


def copy_pairs(transfers, edges):
    """Require each actual transfer to belong to an adjacent unbypassable copy."""
    by_site = {row['site']: row for row in transfers}
    predecessors = {}
    for site, successors in edges.items():
        for successor in successors:
            predecessors.setdefault(successor, set()).add(site)
    paired, pairs = set(), []
    for site, load in sorted(by_site.items()):
        if load['operation'] != 'ldm':
            continue
        store = by_site.get(site + 2)
        if store is None or store['operation'] != 'stm' or \
                store['registers'] != load['registers'] or store['base'] == load['base'] or \
                edges[site] != (site + 2,) or predecessors.get(site + 2) != {site}:
            raise ValueError('block transfers require exact adjacent unbypassable load/store copy pairs')
        paired.update((site, site + 2))
        pairs.append([site, site + 2])
    if paired != set(by_site) or not pairs:
        raise ValueError('every block transfer must belong to an exact load/store copy pair')
    return pairs

def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('scalar switch requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('scalar switch requires immutable exact ROM and index inputs')
    entries = owner.validate_span(data, address, rom, mapping, index)
    refinement = refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement, two_constant_word_switch=True)
    if branches or len(refinement['word_switches']) != 1 or \
            refinement['word_switches'][0].get('interposed_words') != 2 or \
            type(calls) is not dict or calls != actual_calls:
        raise ValueError('scalar switch requires one exact two-constant-word switch and ordinary calls')
    guard_predecessors(instructions, edges, address, refinement['word_switches'][0])
    expected = bind_calls(calls, mapping, address, len(data), len(rom))
    if type(bindings) is not dict or bindings != expected:
        raise ValueError('scalar switch bindings differ from every actual call')
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
    if reached != len(instructions):
        raise ValueError('scalar switch excludes local CFG cycles')
    partition = graph.partition(data, address, refinement, instructions, words)
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    adjustments, transfers = [], []
    for site, instruction in sorted(instructions.items()):
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('block-copy inventory excludes non-ARMv4T instruction widths')
        adjustment = match.thumb_stack_adjustment(instruction)
        if instruction.mnemonic.startswith(('ldm', 'stm')):
            transfers.append(transfer(instruction))
        if instruction.mnemonic not in ('push', 'pop') and adjustment is None and any(
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in instruction.operands):
            raise ValueError('scalar switch excludes stack-address materialization')
        if any(operand.type == ARM_OP_MEM and operand.mem.index == ARM_REG_SP
               for operand in instruction.operands):
            raise ValueError('block-copy inventory excludes SP memory indices')
        if adjustment is not None:
            adjustments.append([site - address, adjustment * 4])
    if not transfers or not {'ldm', 'stm'} <= {row['operation'] for row in transfers}:
        raise ValueError('block-copy inventory requires actual non-SP loads and stores')
    pairs = copy_pairs(transfers, edges)
    if not any(value < 0 for _, value in adjustments):
        raise ValueError('scalar switch requires an actual nonzero fixed local allocation')
    # No buffer contracts, entry-word permissions, alias policies or call
    # preservation overrides. Every return restores the original frame tokens.
    restored = frame.prove_frame(instructions, edges, address, branches, calls)
    switch = refinement['word_switches'][0]
    constant_words = [next(row for row in partition['words'] if row['address'] == address + offset)
                      for offset in (switch['literal'] - 8, switch['literal'] - 4)]
    if any(row['switch_word'] or not row['load_sites'] for row in constant_words):
        raise ValueError('both interposed constants require reached native word loads')
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (thunks, match.divsi3, match.modsi3,
                    match.umodsi3, match.ashldi3, match.software_double, match.software_float)) or \
                not word['switch_word'] and any(int(row['rom'], 16) & ~1 == value & ~1 for row in entries):
            raise ValueError('block-copy inventory cannot materialize runtime/thunk/function addresses')
    modules = (analyze, ordinary, thunks, frame, match, owner, graph, operations, constants)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False, 'address': address, 'end': address + len(data),
        'instructions': len(instructions), 'word_switches': refinement['word_switches'],
        'interposed_constant_words': 2, 'constants': constant_words, 'block_transfers': transfers,
        'copy_pairs': pairs,
        'block_policy': 'exact Thumb16 low-register nonoverlapping-base increment-after transfer; strict frame rejects all SP materialization',
        'memory_safety_claim': False, 'nonalias_claim': False, 'stack_adjustments': adjustments,
        'calls': [[site - address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [], 'ordinary_callee_native_proof': False,
        'ordinary_call_premise': 'conditional: every ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI',
        'caller_facts': 'caller-saved register provenance cleared at every call; no numeric, address, or flags result facts',
        'frame': restored, 'partition': partition,
        'claim': 'complete local structural CFG/frame/return inventory under conditional ordinary returning-call ABI',
        'numeric_input_preconditions': [], 'arithmetic_C_equivalence': False,
        'termination_claim': False,
        'control_flow_guarantee': 'every reached CFG region has a path to a checked return; universal termination is not proved',
        'body_sha256': sha(data), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'ROM_sha256': sha(rom),
        'producer_source_sha256': pins, 'complete_native_structural_proof': True}
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
    refinement = refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement, two_constant_word_switch=True)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
