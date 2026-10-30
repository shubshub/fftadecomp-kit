"""Explicit ABI/effects inventory of canonical signed and unsigned remainder."""
import argparse
import hashlib
import json
from pathlib import Path

import local_long_branch_profile as frame
import match
import modsi3_profile as signed
import owner_admission_profile as owner
import owner_graph_profile as graph
import owner_runtime_profile as operations
import umodsi3_profile as unsigned
from software_double_profile import indices, span_record
from software_float_profile import prove_runtime

SELECTOR = 'unsigned-remainder-structural-inventory-v1'
SCHEMA = 'thumb-canonical-mod-umod-structural-inventory-v1'
ZERO = 0x0814274C
OPERATIONS = {'__modsi3': signed.ADDRESS, '__umodsi3': unsigned.ADDRESS}
SPECS = ((ZERO, 0x0814274E, 1, (), (ZERO,)),
    (unsigned.ADDRESS, 0x08142BE8, 95, ((0x08142BE0, ZERO),),
        (0x08142B32, 0x08142BAE, 0x08142BDC, 0x08142BE6)),
    (signed.ADDRESS, 0x08142A1E, 102, ((0x08142A16, ZERO),), (0x08142A12, 0x08142A1C)))
GUARANTEE = ('Target-state structural ABI/effects at every reached return; '
    'every decoded region has a return path, without universal termination, '
    'arithmetic C-equivalence or result-range claims')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def bind_calls(calls, mapping, address, size, rom_size):
    if type(mapping) is not bytes or type(address) is not int or address % 2 or \
            type(size) is not int or type(rom_size) is not int or size <= 0 or \
            not match.ROM_BASE <= address < address + size <= match.ROM_BASE + rom_size or \
            type(calls) is not dict or set(calls.values()) != set(OPERATIONS.values()) or any(
                type(site) is not int or type(target) is not int or site % 2 or \
                not address <= site <= address + size - 4 for site, target in calls.items()):
        raise ValueError('remainder structural inventory requires exact actual MOD and UMOD calls only')
    names = {target: name for name, target in OPERATIONS.items()}
    return {site: names[target] for site, target in sorted(calls.items())}


def prove_closure(rom, mapping, index):
    """Use the unchanged interpreter and strict frame engine, with no input ranges."""
    from capstone.arm import ARM_OP_MEM, ARM_REG_SP, ARM_REG_R4, ARM_REG_R11
    signed.verify_identity(rom, mapping)
    unsigned.verify_identity(rom, mapping)
    entries, rows = indices(mapping, index)
    proofs, frames, spans = {}, {}, {}
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11 + 1))
    for address, end, count, calls, returns in SPECS:
        span = span_record(address, end, entries, rows, rom)
        if span['instrs'] != count:
            raise ValueError('remainder structural runtime exact dual-index count differs')
        spans[address] = span
        proof = prove_runtime(rom, entries, address, end, count, proofs,
            call_edges=calls, scalar_entries=(address,), allowed_writes=(), thumb_pc_returns=returns)
        if proof['returns'] != list(returns) or proof['writes'] or proof['stack_reads']:
            raise ValueError('remainder structural runtime has incomplete returns or caller-memory effects')
        body = rom[address-match.ROM_BASE:end-match.ROM_BASE]
        refinement = owner.refine(body, address, mapping)
        instructions, edges, branches, actual_calls, words = graph.graph(body, address, refinement)
        if branches or words or any(op.mem.base != ARM_REG_SP or op.mem.index
                for instruction in instructions.values() for op in instruction.operands if op.type == ARM_OP_MEM):
            raise ValueError('remainder structural runtime has a nonstack memory access')
        restored = frame.prove_frame(instructions, edges, address, {}, actual_calls,
            call_preservation={site: preserved for site in actual_calls})
        if restored['returns'] != list(returns):
            raise ValueError('remainder structural runtime frame return coverage differs')
        frames[address] = {'frame': restored,
            'maximum_additional_stack_bytes': restored['maximum_frame_bytes'] + max(
                (frames[target]['maximum_additional_stack_bytes'] for target in actual_calls.values()), default=0),
            'external_writes': [], 'incoming_stack_reads': [], 'nonstack_memory_reads': []}
        proofs[address] = proof
    return {'native_runtime_closure': [[site, proof] for site, proof in sorted(proofs.items())],
        'native_runtime_frames': [[site, proof] for site, proof in sorted(frames.items())],
        'runtime_spans': [[site, span] for site, span in sorted(spans.items())]}


def verify(data, address, rom, mapping, index, calls, bindings, *, selector, manifest=None):
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('remainder structural inventory requires its explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('remainder structural inventory requires immutable exact ROM/index inputs')
    owner.validate_span(data, address, rom, mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, actual_calls, words = graph.graph(data, address, refinement)
    if branches or words or calls != actual_calls or type(bindings) is not dict or \
            bindings != bind_calls(calls, mapping, address, len(data), len(rom)):
        raise ValueError('remainder structural inventory requires exact complete runtime bindings and CFG')
    entries, rows = indices(mapping, index)
    if span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('remainder structural caller dual-index count differs from its native CFG')
    partition = graph.partition(data, address, refinement, instructions, words)
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    observed = prove_closure(rom, mapping, index)
    from capstone.arm import ARM_REG_R4, ARM_REG_R11
    preserved = frozenset(range(ARM_REG_R4, ARM_REG_R11 + 1))
    restored = frame.prove_frame(instructions, edges, address, {}, calls, stack_aliases=True,
        call_preservation={site: preserved for site in calls})
    observed.update(schema=SCHEMA, selector=SELECTOR, inventory_only=True,
        source_or_ELF_admission=False, structural_guarantee=GUARANTEE,
        arithmetic_C_equivalence_proved=False, result_ranges_proved=False,
        universal_termination_proved=False, numeric_operand_preconditions=[],
        entry_stack_contract=None, ordinary_calls=[], ordinary_call_ABI=None,
        external_call_policy='complete native canonical MOD/UMOD/zero ABI and frame effects only',
        caller_facts='no quotient, remainder, numeric or flags result facts',
        runtime_stack_policy='canonical runtimes access only their proved frames below caller SP',
        frame=restored, partition=partition, instructions=len(instructions), address=address, end=address+len(data),
        calls=[[site-address, name] for site, name in sorted(bindings.items())],
        dependencies={'signed': [list(row) for row in signed.IDENTITIES],
            'unsigned': [list(row) for row in unsigned.IDENTITIES]},
        body_sha256=sha(data), mapping_sha256=sha(mapping), index_sha256=sha(index), ROM_sha256=sha(rom),
        complete_native_proof=True)
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('remainder structural inventory manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'],16) == args.address]
    if len(rows) != 1:
        raise ValueError('remainder structural inventory requires one exact mapped owner')
    data = rom[args.address-match.ROM_BASE:int(rows[0]['end'],16)-match.ROM_BASE]
    refinement = owner.refine(data, args.address, mapping)
    _, _, _, calls, _ = graph.graph(data, args.address, refinement)
    bindings = bind_calls(calls, mapping, args.address, len(data), len(rom))
    manifest, _ = verify(data, args.address, rom, mapping, index, calls, bindings, selector=args.profile)
    print(text(manifest))


if __name__ == '__main__':
    main()
