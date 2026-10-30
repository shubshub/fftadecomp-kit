"""Explicit private-float pack-only argument-effect inventory, without source admission."""
import argparse
import hashlib
import json
from pathlib import Path

import software_float_profile as runtime
import private_float_pack_effects_inventory as pack_base

SELECTOR = 'private-float-pack-only-effects-inventory-v1'
SCHEMA = 'thumb-private-float-pack-only-effects-inventory-v1'
EFFECT_SCHEMA = pack_base.EFFECT_SCHEMA
BUFFER_PREMISE = pack_base.BUFFER_PREMISE
policy = pack_base.policy


HELPERS = (pack_base.HELPERS[1],)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def verify(data, address, rom, mapping, index, *, selector, manifest=None):
    import match
    import owner_admission_profile as owner
    import owner_graph_profile as graph
    import owner_runtime_profile as operations
    from capstone import Cs, CS_ARCH_ARM, CS_MODE_THUMB
    from software_double_profile import indices, span_record
    if type(selector) is not str or selector != SELECTOR:
        raise ValueError('private float effects require their explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('private float effects require exact immutable typed inputs')
    if sha(rom) != runtime.ROM_SHA256:
        raise ValueError('private float effects require the approved complete ROM identity')
    owner.validate_span(data, address, rom, mapping, index)
    entries, rows = indices(mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
    expected_targets = [HELPERS[0][1][0]]
    if branches or words or [target for _, target in sorted(calls.items())] != expected_targets:
        raise ValueError('private float effects require exactly one pinned pack and no other calls')
    if span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('private float caller complete dual-index count differs')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    partition = graph.partition(data, address, refinement, instructions, words)
    dependencies, helper_records = {}, []
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    for name, (start, end, count, digest), bounds in HELPERS:
        record = span_record(start, end, entries, rows, rom)
        body = rom[start-match.ROM_BASE:end-match.ROM_BASE]
        if record['instrs'] != count or sha(body) != digest or start < address+len(data) and end > address:
            raise ValueError('private float helper complete body/count/ownership identity differs')
        actual_edges = [(site, target) for site, target in runtime.EDGES if start <= site < end]
        if actual_edges:
            raise ValueError('private float helper requires a fully closed leaf dependency')
        proof = runtime.prove_runtime(rom, entries, start, end, count, {}, call_edges=(),
            scalar_entries=(), argument_effect_policy=bounds)
        dependencies[start] = proof
        decoded = {item.address: item for lo, hi in proof['layout']['code_ranges']
                   for item in decoder.disasm(rom[int(lo, 16)-match.ROM_BASE:int(hi, 16)-match.ROM_BASE], int(lo, 16))}
        body_partition = graph.partition(body, start, proof['layout'], decoded, {})
        if len(decoded) != count or set(decoded) != {site for site, _ in proof['native_edges']}:
            raise ValueError('private float helper native CFG and complete partition differ')
        helper_records.append({'name': name, 'address': start, 'end': end, 'instructions': count,
            'body_sha256': digest, 'calls': actual_edges, 'native_proof': proof,
            'partition': body_partition, 'conditional_buffer_premise': BUFFER_PREMISE})
    caller = runtime.prove_runtime(rom, entries, address, address+len(data), len(instructions),
        dependencies, call_edges=tuple(sorted(calls.items())), scalar_entries=(address,),
        argument_effect_policy=policy())
    if caller['argument_effects']['reads'] or caller['writes'] or caller['stack_reads']:
        raise ValueError('private float caller has undischarged external or incoming effects')
    if caller['native_edges'] != [[site, list(targets)] for site, targets in sorted(edges.items())]:
        raise ValueError('private float caller native and complete CFG edges differ')
    # Every actual propagated access must have been checked as a live local stack access.
    if not caller['argument_accesses'] or any(item[-1][:2] != ['stack', 0]
                                             for item in caller['argument_accesses']):
        raise ValueError('private float caller must discharge actual helper effects into allocated locals')
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes())
                   for module in (runtime, pack_base, match, owner, graph, operations)}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'complete_native_structural_proof': True, 'complete_argument_effect_proof': True,
        'address': address, 'end': address+len(data), 'instructions': len(instructions),
        'body_sha256': sha(data), 'ROM_sha256': sha(rom),
        'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
        'private_bindings': [[site, next(name for name, record, _ in HELPERS if record[0] == target)]
                             for site, target in sorted(calls.items())],
        'helper_closure': helper_records, 'caller': caller, 'partition': partition,
        'external_reads': caller['argument_effects']['reads'], 'external_writes': caller['writes'],
        'conditional_helper_buffer_premise': BUFFER_PREMISE,
        'caller_discharged_helper_effects_into_live_abstract_locals': True,
        'numeric_input_preconditions': [], 'numeric_return_facts': [],
        'source_or_ELF_admission': False, 'arithmetic_C_equivalence': False,
        'memory_safety_claim': False, 'physical_memory_claim': False,
        'nonescape_claim': False, 'universal_termination_claim': False,
        'claim': 'complete abstract CFG, reached-return restoration and actual finite argument-read/write bounds; loaded values unknown',
        'producer_source_sha256': source_pins}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('private float argument-effect manifest differs from fresh native proof')
    return observed, [instructions[site] for site in sorted(instructions)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, choices=(SELECTOR,))
    for name in ('rom', 'mapping', 'index'):
        parser.add_argument('--'+name, required=True, type=Path)
    parser.add_argument('address', type=lambda value: int(value, 16))
    args = parser.parse_args()
    rom, mapping, index = args.rom.read_bytes(), args.mapping.read_bytes(), args.index.read_bytes()
    rows = [row for row in json.loads(mapping) if int(row['rom'], 16) == args.address]
    if len(rows) != 1:
        raise ValueError('private float effects require one exact mapped caller')
    data = rom[args.address-0x08000000:int(rows[0]['end'], 16)-0x08000000]
    result, _ = verify(data, args.address, rom, mapping, index, selector=args.profile)
    print(text(result))


if __name__ == '__main__':
    main()
