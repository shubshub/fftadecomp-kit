"""Explicit saved-only canonical MOD structural inventory with optional ordinary calls."""
import argparse
import hashlib
import json
from pathlib import Path

from capstone.arm import ARM_OP_MEM, ARM_OP_REG, ARM_REG_SP

import modsi3_profile as remainder

SELECTOR = 'mod-only-saved-only-structural-inventory-v1'
SCHEMA = 'thumb-mod-only-saved-only-structural-inventory-v1'
ZERO = 0x0814274C


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
                not address <= site <= address + size - 4 for site, target in calls.items()):
        raise ValueError('MOD-only inventory requires exact typed actual call sites')
    entries = json.loads(mapping)
    if type(entries) is not list or any(type(row) is not dict for row in entries):
        raise ValueError('MOD-only inventory requires a function mapping list')
    bindings = {}
    for site, target in sorted(calls.items()):
        if target == remainder.ADDRESS:
            bindings[site] = '__modsi3'
            continue
        if match.function_thunk.reserved(target):
            raise ValueError('MOD-only ordinary calls exclude reserved call thunks')
        name = f'func_{target:08X}'
        actual = match.function_address_target(name, entries, address, size, rom_size)
        row = next(row for row in entries if int(row['rom'], 16) == actual)
        end = int(row['end'], 16)
        if not actual < end <= match.ROM_BASE + rom_size or \
                actual < address + size and end > address or any(
                    other is not row and int(other['rom'], 16) < end and
                    int(other['end'], 16) > actual for other in entries):
            raise ValueError('MOD-only ordinary calls require unique nonoverlapping mapped spans')
        bindings[site] = name
    if '__modsi3' not in bindings.values():
        raise ValueError('MOD-only inventory requires an actual canonical MOD call')
    return bindings


def runtime_frames(rom, mapping, closure):
    """Independently check exact MOD/zero frames without incoming memory permission."""
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import local_long_branch_profile as frame
    from capstone.arm import ARM_REG_R4, ARM_REG_R11
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11 + 1))
    proven = {}
    for address, end, expected_calls in ((ZERO, ZERO + 2, {}),
            (remainder.ADDRESS, 0x08142A1E, {0x08142A16: ZERO})):
        data = rom[address - 0x08000000:end - 0x08000000]
        refinement = owner.refine(data, address, mapping)
        instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
        if branches or words or calls != expected_calls or any(target not in proven for target in calls.values()) or \
                closure[address]['writes'] or closure[address]['stack_reads'] or any(
                    operand.mem.base != ARM_REG_SP or operand.mem.index
                    for instruction in instructions.values() for operand in instruction.operands
                    if operand.type == ARM_OP_MEM):
            raise ValueError('MOD-only runtime requires exact dependencies and no caller-memory effects')
        restored = frame.prove_frame(instructions, edges, address, {}, calls,
            call_preservation={site: preserved for site in calls})
        if restored['returns'] != closure[address]['returns']:
            raise ValueError('MOD-only runtime frame return coverage differs')
        proven[address] = {'frame': restored,
            'maximum_additional_stack_bytes': restored['maximum_frame_bytes'] + max(
                (proven[target]['maximum_additional_stack_bytes'] for target in calls.values()), default=0),
            'caller_memory_writes': [], 'caller_stack_reads': [], 'nonstack_memory_reads': [],
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
        raise ValueError('MOD-only inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or \
            type(address) is not int or type(calls) is not dict or type(bindings) is not dict:
        raise ValueError('MOD-only inventory requires immutable exact bytes and typed call records')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('MOD-only inventory requires its exact complete direct-call CFG and bindings')
    entries, rows = canonical.indices(mapping, index)
    if canonical.span_record(address, address + len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('MOD-only inventory requires exact dual-index reachable instruction counts')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    for instruction in instructions.values():
        if instruction.size != 2 and not (instruction.mnemonic == 'bl' and instruction.size == 4):
            raise ValueError('MOD-only inventory excludes non-ARMv4T widths')
        if match.uses_stack_frame((instruction,)) or instruction.mnemonic.startswith(('ldm', 'stm')) or any(
                operand.type == ARM_OP_MEM and
                (operand.mem.base == ARM_REG_SP or operand.mem.index == ARM_REG_SP) or
                instruction.mnemonic not in ('push', 'pop') and
                operand.type == ARM_OP_REG and operand.reg == ARM_REG_SP
                for operand in instruction.operands):
            raise ValueError('MOD-only saved-only inventory excludes allocation, SP accesses/exports and block transfers')
    partition = graph.partition(data, address, refinement, instructions, words)
    for word in partition['words']:
        value = word['value']
        if value in match.RUNTIME_HELPERS.values() or match.function_thunk.reserved(value) or \
                match.is_udivsi3_address(value) or any(module.reserved(value) for module in
                (remainder, match.divsi3, match.umodsi3, match.ashldi3, canonical, native)):
            raise ValueError('MOD-only inventory cannot materialize runtime or thunk addresses')
    closure = canonical.prove_remainder_closure(rom, mapping, index)
    if set(closure) != {remainder.ADDRESS, ZERO} or \
            closure[remainder.ADDRESS]['returns'] != [0x08142A12, 0x08142A1C] or \
            closure[ZERO]['returns'] != [ZERO] or any(
                proof['writes'] or proof['stack_reads'] for proof in closure.values()):
        raise ValueError('MOD-only inventory requires complete exact MOD/zero native closures')
    native_frames = runtime_frames(rom, mapping, closure)
    restored = frame.prove_frame(instructions, edges, address, {}, calls)
    modules = (match, owner, graph, operations, frame, canonical, native, remainder)
    sources = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes()) for module in modules}
    sources[Path(__file__).name] = sha(Path(__file__).read_bytes())
    ordinary = [[site - address, name] for site, name in sorted(bindings.items()) if name != '__modsi3']
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'source_or_ELF_admission': False,
        'claim': 'structural target-state ABI/effects at reached returns under complete MOD/zero closure and conditional ordinary returning-call ABI',
        'runtime_entry_domain': 'arbitrary32-bit entry-register patterns; no numeric preconditions',
        'runtime_input_semantics': 'unchanged native interpreter symbolic entry-register origins including actual zero-hook path',
        'arithmetic_C_equivalence': False, 'memory_safety_claim': False,
        'physical_stack_nonalias_claim': False, 'physical_memory_preservation_claim': False,
        'runtime_numeric_return_facts': [], 'numeric_operand_preconditions': [], 'nonzero_facts': [],
        'termination_claim': False,
        'control_flow_guarantee': 'every reached CFG region has a path to a checked return; universal termination is not proved',
        'dependencies': [list(row) for row in remainder.IDENTITIES],
        'native_runtime_closure': [[site, proof] for site, proof in sorted(closure.items())],
        'native_runtime_frames': native_frames,
        'calls': [[site - address, name] for site, name in sorted(bindings.items())],
        'runtime_calls': [[site - address, name] for site, name in sorted(bindings.items()) if name == '__modsi3'],
        'ordinary_calls': ordinary, 'indirect_calls': [],
        'ordinary_call_premise': ('conditional: each ordinary callee returns and obeys existing r4-r11/SP preserving direct-call ABI; no native ordinary-callee proof' if ordinary else None),
        'caller_facts': 'every call clears caller-saved provenance; no numeric/address/flags result facts supplied',
        'caller_frame_policy': 'strict saved slots, SP, r4-r11 and entry-LR restoration; no local allocation, explicit SP access/export, entry-word or buffer permission',
        'runtime_stack_policy': 'canonical MOD/zero accesses only its independently proved own frames below caller SP in the existing abstract stack model',
        'ordinary_call_stack_bound': None, 'entry_stack_contract': None,
        'frame': restored, 'partition': partition, 'instructions': len(instructions),
        'body_sha256': sha(data), 'ROM_sha256': sha(rom), 'mapping_sha256': sha(mapping),
        'index_sha256': sha(index), 'producer_source_sha256': sources,
        'complete_native_structural_proof': True}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('MOD-only inventory manifest differs from fresh native proof')
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
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('MOD-only inventory requires one exact mapped owner')
    data = rom[args.address - 0x08000000:int(rows[0]['end'], 16) - 0x08000000]
    _, _, _, calls, _ = graph.graph(data, args.address, owner.refine(data, args.address, mapping))
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    observed, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(observed))


if __name__ == '__main__':
    main()
