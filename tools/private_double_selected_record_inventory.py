"""Explicit private-double unpack/selected-record/pack argument-effect inventory, without source admission."""
import argparse
import hashlib
import json
from pathlib import Path

import software_float_profile as runtime
import software_double_profile as double
import private_double_pack_effects_inventory as double_pack
import private_float_argument_effects_inventory as argument_base

SELECTOR = 'private-double-selected-record-effects-inventory-v1'
SCHEMA = 'thumb-private-double-selected-record-effects-inventory-v1'
EFFECT_SCHEMA = argument_base.EFFECT_SCHEMA
BUFFER_PREMISE = argument_base.BUFFER_PREMISE
policy = argument_base.policy


FIXED_RECORD = 0x03005E50
FIXED_RECORD_ORIGIN = (0x08142E62, 0x08142E68)
ABSOLUTE_POLICY = {'schema': 'thumb-conditional-absolute-reads-v1',
    'reads': [[FIXED_RECORD+offset, 4] for offset in range(0, 20, 4)]}
RETURN_POINTERS = [['argument', number, 0] for number in range(3)] + [['constant', FIXED_RECORD, 0]]
CONTRACT = ('pinned unpack/selected-record/pack finite effects and returned pointer provenance; '
            'fixed RAM record readability is a conditional premise, its contents unknown; '
            'initialized contents, IEEE and C definedness equivalence, physical memory, '
            'nonalias, nonescape and universal termination unproved')
# Dependency order is explicit; no scalar result is assigned a numeric value.
HELPERS = (
    double_pack.HELPERS[0],
    ('private-wide-negation', next(record for record in double.IDENTITIES if record[0] == 0x08142A94), policy()),
    ('private-selection', next(record for record in double.IDENTITIES if record[0] == 0x08142E10),
     policy(((number, offset, 4) for number in range(3) for offset in range(0, 20, 4)),
            ((2, offset, 4) for offset in range(0, 20, 4)))),
    double_pack.HELPERS[1],
    double_pack.HELPERS[2],
)
ROOT_HELPERS = ('private-unpack', 'private-unpack', 'private-selection', 'private-pack')



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
        raise ValueError('private double effects require their explicit inventory-only selector')
    if any(type(value) is not bytes for value in (data, rom, mapping, index)) or type(address) is not int:
        raise ValueError('private double effects require exact immutable typed inputs')
    if sha(rom) != runtime.ROM_SHA256:
        raise ValueError('private double effects require the approved complete ROM identity')
    owner.validate_span(data, address, rom, mapping, index)
    entries, rows = indices(mapping, index)
    refinement = owner.refine(data, address, mapping)
    instructions, edges, branches, calls, words = graph.graph(data, address, refinement)
    expected_targets = [next(record[0] for role, record, _ in HELPERS if role == name)
                        for name in ROOT_HELPERS]
    if branches or words or [target for _, target in sorted(calls.items())] != expected_targets:
        raise ValueError('private double effects require exactly two pinned unpacks, one selected-record helper and one pack')
    if span_record(address, address+len(data), entries, rows, rom)['instrs'] != len(instructions):
        raise ValueError('private double caller complete dual-index count differs')
    operations.verify_operations(instructions, edges, address, branches, calls, refinement)
    partition = graph.partition(data, address, refinement, instructions, words)
    dependencies, helper_records = {}, []
    decoder = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    decoder.detail = True
    for name, (start, end, count, digest), bounds in HELPERS:
        record = span_record(start, end, entries, rows, rom)
        body = rom[start-match.ROM_BASE:end-match.ROM_BASE]
        if record['instrs'] != count or sha(body) != digest or start < address+len(data) and end > address:
            raise ValueError('private double helper complete body/count/ownership identity differs')
        actual_edges = [(site, target) for site, target in double.EDGES if start <= site < end]
        if any(target not in dependencies for _, target in actual_edges):
            raise ValueError('private double helper lacks a completed native dependency')
        proof = runtime.prove_runtime(rom, entries, start, end, count, dependencies,
            call_edges=tuple(actual_edges), scalar_entries=(), argument_effect_policy=bounds,
            stack_load_widths=(1, 2, 4) if name in ('private-unpack', 'private-pack') else (4,),
            stack_store_widths=(1, 2, 4) if name == 'private-pack' else (4,),
            return_pointer_policy=RETURN_POINTERS if name == 'private-selection' else None)
        dependencies[start] = proof
        decoded = {item.address: item for lo, hi in proof['layout']['code_ranges']
                   for item in decoder.disasm(rom[int(lo, 16)-match.ROM_BASE:int(hi, 16)-match.ROM_BASE], int(lo, 16))}
        body_partition = graph.partition(body, start, proof['layout'], decoded, {})
        if len(decoded) != count or set(decoded) != {site for site, _ in proof['native_edges']}:
            raise ValueError('private double helper native CFG and complete partition differ')
        if name == 'private-selection':
            # The fixed address is authenticated as an actual reached PC literal,
            # not supplied as an arbitrary readable address or inferred extent.
            site, literal = FIXED_RECORD_ORIGIN
            item = decoded.get(site)
            if item is None or item.mnemonic != 'ldr' or len(item.operands) != 2 or \
                    item.operands[0].type != match.ARM_OP_REG or item.operands[0].reg != match.ARM_REG_R0 or \
                    item.operands[1].type != match.ARM_OP_MEM or item.operands[1].mem.base != match.ARM_REG_PC or \
                    item.operands[1].mem.index or ((site+4) & ~3)+item.operands[1].mem.disp != literal or \
                    not start <= literal <= end-4 or \
                    int.from_bytes(body[literal-start:literal-start+4], 'little') != FIXED_RECORD:
                raise ValueError('private double fixed record lacks its actual reached literal identity')
            if proof['return_pointers']['values'] != RETURN_POINTERS:
                raise ValueError('private double selection must retain all three formals and exact constant')
        helper_records.append({'name': name, 'address': start, 'end': end, 'instructions': count,
            'body_sha256': digest, 'calls': actual_edges, 'native_proof': proof,
            'partition': body_partition, 'conditional_buffer_premise': BUFFER_PREMISE})
    caller = runtime.prove_runtime(rom, entries, address, address+len(data), len(instructions),
        dependencies, call_edges=tuple(sorted(calls.items())), scalar_entries=(address,),
        argument_effect_policy=policy(), compose_pointer_returns=True,
        absolute_read_policy=ABSOLUTE_POLICY)
    if caller['argument_effects']['reads'] or caller['writes'] or caller['stack_reads']:
        raise ValueError('private double caller has undischarged external or incoming effects')
    if caller['native_edges'] != [[site, list(targets)] for site, targets in sorted(edges.items())]:
        raise ValueError('private double caller native and complete CFG edges differ')
    # Local alternatives were each checked against the live frame by runtime;
    # the only other read permission is the explicitly conditional fixed record.
    if not caller['argument_accesses'] or caller['absolute_reads']['reads'] != ABSOLUTE_POLICY['reads']:
        raise ValueError('private double selected-record caller must retain all actual conditional fixed reads')
    source_pins = {Path(module.__file__).name: sha(Path(module.__file__).read_bytes())
                   for module in (runtime, double, double_pack, argument_base, match, match.armv4t, owner, graph, operations)}
    source_pins[Path(__file__).name] = sha(Path(__file__).read_bytes())
    observed = {'schema': SCHEMA, 'selector': SELECTOR, 'inventory_only': True,
        'complete_native_structural_proof': True, 'complete_argument_effect_proof': True,
        'address': address, 'end': address+len(data), 'instructions': len(instructions),
        'body_sha256': sha(data), 'ROM_sha256': sha(rom),
        'mapping_sha256': sha(mapping), 'index_sha256': sha(index),
        'private_bindings': [[site, next(name for name, record, _ in HELPERS if record[0] == target)]
                             for site, target in sorted(calls.items())],
        'helper_closure': helper_records, 'caller': caller, 'partition': partition,
        'fixed_record_identity': {'address': FIXED_RECORD, 'literal_load': FIXED_RECORD_ORIGIN[0],
            'literal_word': FIXED_RECORD_ORIGIN[1], 'extent_or_readability_proved': False},
        'external_reads': caller['absolute_reads']['reads'],
        'external_formal_reads': caller['argument_effects']['reads'], 'external_writes': caller['writes'],
        'conditional_helper_buffer_premise': BUFFER_PREMISE,
        'caller_discharged_helper_effects_into_live_abstract_locals': False,
        'caller_effects_bound_by_live_locals_and_conditional_fixed_record': True,
        'conditional_absolute_read_premise': caller['absolute_reads'],
        'numeric_input_preconditions': [], 'numeric_return_facts': [],
        'source_or_ELF_admission': False, 'arithmetic_C_equivalence': False,
        'memory_safety_claim': False, 'physical_memory_claim': False,
        'nonescape_claim': False, 'universal_termination_claim': False,
        'claim': 'complete abstract CFG, reached-return restoration, finite returned-pointer provenance and conditional argument/absolute-read bounds; loaded values unknown',
        'producer_source_sha256': source_pins}
    if manifest is not None and text(manifest) != text(observed):
        raise ValueError('private double argument-effect manifest differs from fresh native proof')
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
        raise ValueError('private double effects require one exact mapped caller')
    data = rom[args.address-0x08000000:int(rows[0]['end'], 16)-0x08000000]
    result, _ = verify(data, args.address, rom, mapping, index, selector=args.profile)
    print(text(result))


if __name__ == '__main__':
    main()
