"""Explicit plain scalar-frame DIV/zero and canonical-r4 structural inventory."""
import argparse
import hashlib
import json
from pathlib import Path

from capstone.arm import ARM_OP_REG, ARM_REG_SP

import analyze
import div_thunk_zero_word_switch_inventory as guarded
import divsi3_profile as quotient
import div_only_ordinary_inventory as division
import software_double_profile as canonical
import software_float_profile as native
import function_thunk_profile as thunks
import local_long_branch_profile as frame
import match
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations

SELECTOR = 'plain-div-r4-thunk-inventory-v1'
SCHEMA = 'thumb-plain-div-r4-thunk-inventory-v1'
THUNK = '_call_via_r4'
THUNK_ADDRESS = thunks.ALIASES[THUNK]
ZERO = division.ZERO


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def sha(value):
    return hashlib.sha256(value).hexdigest()


def bind_calls(calls, mapping, address, size, rom_size):
    """Keep the existing exact DIV/r4/ordinary binding and reserved-target gates."""
    return guarded.bind_calls(calls, mapping, address, size, rom_size)


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('plain DIV/r4 inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('plain DIV/r4 inventory requires immutable exact ROM and index inputs')
    entries = owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or refinement['word_switches'] or type(calls) is not dict or calls != actual_calls:
        raise ValueError('plain DIV/r4 inventory excludes switches and local BL, and requires every actual call')
    expected = bind_calls(calls, mapping, address, len(data), len(rom))
    if type(bindings) is not dict or bindings != expected:
        raise ValueError('plain DIV/r4 inventory bindings differ from every actual call')
    selected = next(row for row in entries if int(row['rom'], 16) == address)
    rows = [line.split() for line in index.decode().splitlines()
            if line.split() and line.split()[0] == f'{address:08X}']
    if type(selected.get('instrs')) is not int or selected['instrs'] != len(instructions) or \
            len(rows) != 1 or len(rows[0]) < 4 or int(rows[0][3]) != len(instructions):
        raise ValueError('plain DIV/r4 inventory requires exact dual-index reachable instruction counts')
    runtime = {site: name for site, name in bindings.items() if name in thunks.ALIASES}
    dependencies = thunks.dependencies(runtime.values(), rom)
    # Preserve existing typed PC-literal provenance; no code-entry word may be
    # silently reclassified as data by this inventory composition.
    thunks.verify_literal_bindings(data, address, instructions.values(), calls, mapping, {})
    # Record cycles without deleting edges or setting an iteration cutoff.
    # Existing graph return-connectedness and the finite frame fixpoint remain mandatory.
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
    cyclic = reached != len(instructions)
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or match.is_udivsi3_address(value) or any(
                module.reserved(value) for module in (thunks, quotient, match.modsi3,
                    match.umodsi3, match.ashldi3, canonical, native)):
            raise ValueError('DIV/plain DIV/r4 inventory cannot materialize runtime or thunk addresses')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    adjustments = []
    for site, instruction in sorted(instructions.items()):
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('plain DIV/r4 inventory excludes non-ARMv4T widths')
        adjustment = match.thumb_stack_adjustment(instruction)
        if instruction.mnemonic.startswith(('ldm', 'stm')):
            raise ValueError('plain DIV/r4 inventory excludes block transfers')
        if instruction.mnemonic not in ('push', 'pop') and adjustment is None and any(
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in instruction.operands):
            raise ValueError('plain DIV/r4 inventory excludes stack-address materialization')
        if adjustment is not None:
            adjustments.append([site - address, adjustment * 4])
    if not any(value < 0 for _, value in adjustments):
        raise ValueError('plain DIV/r4 inventory requires an actual nonzero fixed local allocation')
    closure = canonical.prove_division_closure(rom, mapping, index)
    if set(closure) != {quotient.ADDRESS, ZERO} or \
            closure[quotient.ADDRESS]['returns'] != [0x0814273E, 0x08142748] or \
            closure[ZERO]['returns'] != [ZERO] or any(
                proof['writes'] or proof['stack_reads'] for proof in closure.values()):
        raise ValueError('DIV/plain DIV/r4 inventory requires complete exact DIV/zero native closures')
    native_frames = division.runtime_frames(rom, mapping, closure)
    # Canonical DIV/zero has an exact independent preservation/effects proof.
    # Ordinary and canonical indirect calls retain their conditional ABI. No
    # buffer, incoming-word, alias, or additional preservation policy is granted.
    restored = frame.prove_frame(instructions, edges, address, branches, calls,
        runtime_calls=runtime)
    modules = (analyze, thunks, frame, match, owner, graph, operations, quotient,
        division, canonical, native, guarded)
    pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False, 'address': address, 'end': address + len(data),
        'instructions': len(instructions), 'word_switches': refinement['word_switches'],
        'interposed_constant_words': 0, 'stack_adjustments': adjustments,
        'cyclic_CFG': cyclic, 'CFG_edges': [[site-address, [target-address for target in successors]]
            for site, successors in sorted(edges.items())],
        'cycle_policy': 'all actual edges retained; existing finite native frame fixpoint; every reached region has a return path; no iteration cutoff or universal termination claim',
        'entry_stack_permissions': [], 'buffer_permissions': [],
        'calls': [[site - address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site - address, name] for site, name in sorted(runtime.items())],
        'canonical_thunk_runtime': thunks.RUNTIME, 'canonical_thunk_ABI': thunks.ABI,
        'canonical_thunk_dependencies': dependencies,
        'division_calls': [[site - address, name] for site, name in sorted(bindings.items()) if name == '__divsi3'],
        'ordinary_calls': [[site - address, name] for site, name in sorted(bindings.items()) if name.startswith('func_')],
        'division_dependencies': [list(row) for row in canonical.DIVISION_IDENTITIES],
        'native_runtime_closure': [[site, proof] for site, proof in sorted(closure.items())],
        'native_runtime_frames': native_frames,
        'runtime_stack_policy': 'complete DIV/actual-zero closures access only their own proved frame below current caller SP; no caller-stack read or external write',
        'runtime_entry_domain': 'arbitrary32-bit entry-register patterns; no numeric preconditions',
        'runtime_numeric_return_facts': [], 'nonzero_facts': [],
        'indirect_callee_native_proof': False, 'indirect_callee_effect_proof': False,
        'indirect_call_premise': 'conditional: the indirect target returns and obeys the existing r4-r11/SP preserving ARM ABI; its body, memory effects and target-state validity are not proved',
        'ordinary_callee_native_proof': False,
        'ordinary_call_premise': 'conditional: every ordinary callee returns and obeys the existing r4-r11/SP preserving direct-call ABI',
        'caller_facts': 'caller-saved register provenance cleared at every call; no numeric, address, or flags result facts',
        'frame': restored, 'partition': partition,
        'claim': 'local structural reached-return ABI/effects inventory under complete canonical DIV/zero closure and conditional ordinary and canonical indirect returning-call ABI',
        'caller_frame_policy': 'fixed scalar locals/saved slots/SP/r4-r11/entry-LR; no aliases, SP exports, entry-word or buffer permissions',
        'ordinary_call_stack_bound': None,
        'numeric_input_preconditions': [], 'arithmetic_C_equivalence': False,
        'memory_safety_claim': False,
        'termination_claim': False,
        'control_flow_guarantee': 'every reached CFG region has a path to a checked return; universal termination is not proved',
        'body_sha256': sha(data), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'ROM_sha256': sha(rom),
        'producer_source_sha256': pins, 'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('plain DIV/r4 inventory manifest differs from fresh native proof')
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
        raise ValueError('plain DIV/r4 inventory requires one exact mapped owner')
    data = rom[args.address - match.ROM_BASE:int(rows[0]['end'], 16) - match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
